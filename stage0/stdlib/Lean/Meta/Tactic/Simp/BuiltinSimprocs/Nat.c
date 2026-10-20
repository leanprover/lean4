// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
// Imports: public import Init.Simproc public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util public import Lean.Meta.LitValues public import Lean.Meta.Offset import Lean.Util.SafeExponentiation import Init.Data.Nat.Dvd import Init.Data.Nat.PowMod import Init.Data.Nat.Simproc
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstAdd;
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_powmod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(103, 57, 115, 133, 251, 27, 153, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceSucc___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceLog2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "log2"};
static const lean_object* l_Nat_reduceLog2___redArg___closed__0 = (const lean_object*)&l_Nat_reduceLog2___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceLog2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLog2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLog2___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceLog2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 28, 147, 205, 160, 10, 161, 183)}};
static const lean_object* l_Nat_reduceLog2___redArg___closed__1 = (const lean_object*)&l_Nat_reduceLog2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_reduceLog2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLog2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLog2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLog2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceLog2"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(246, 49, 5, 115, 208, 139, 88, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceLog2___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(209, 55, 73, 242, 185, 51, 64, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(167, 230, 249, 145, 254, 156, 61, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(171, 95, 24, 58, 17, 176, 174, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(231, 215, 207, 13, 249, 183, 176, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(183, 226, 154, 210, 11, 244, 146, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducePow"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(60, 231, 124, 151, 108, 38, 1, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reducePow___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Nat_reducePowMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "powMod"};
static const lean_object* l_Nat_reducePowMod___redArg___closed__0 = (const lean_object*)&l_Nat_reducePowMod___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reducePowMod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reducePowMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reducePowMod___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reducePowMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 205, 101, 55, 99, 18, 171, 194)}};
static const lean_object* l_Nat_reducePowMod___redArg___closed__1 = (const lean_object*)&l_Nat_reducePowMod___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_reducePowMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePowMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePowMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePowMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reducePowMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(151, 45, 80, 7, 48, 46, 107, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reducePowMod___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(148, 61, 72, 84, 221, 248, 138, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceAnd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceXor"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(247, 188, 94, 215, 20, 109, 242, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceXor___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceOr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(221, 174, 173, 61, 215, 145, 106, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceOr___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(207, 233, 59, 9, 218, 201, 108, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(243, 57, 160, 187, 200, 59, 234, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceShiftRight___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Nat_reduceGcd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gcd"};
static const lean_object* l_Nat_reduceGcd___redArg___closed__0 = (const lean_object*)&l_Nat_reduceGcd___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceGcd___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceGcd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceGcd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 94, 240, 174, 21, 113, 54, 0)}};
static const lean_object* l_Nat_reduceGcd___redArg___closed__1 = (const lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceGcd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(82, 32, 179, 68, 111, 80, 212, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(226, 122, 83, 255, 56, 112, 58, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(188, 136, 66, 184, 194, 15, 6, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(103, 209, 103, 202, 56, 43, 177, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Nat_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Nat_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(177, 23, 93, 29, 19, 120, 61, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(190, 70, 159, 136, 109, 243, 67, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_isValue___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_decide_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_decide_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_eq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_eq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_add_gt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 49, 75, 205, 14, 153, 197, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(151, 221, 155, 114, 230, 4, 170, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_eq_gt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(222, 96, 15, 118, 250, 229, 166, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_eq_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(251, 19, 99, 115, 28, 102, 68, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_eq_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(63, 34, 5, 84, 182, 212, 65, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_eq_add_ge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(145, 96, 71, 238, 158, 249, 159, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceEqDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(254, 236, 88, 131, 52, 249, 43, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBeqDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "beqFalseOfEqFalse"};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 37, 109, 252, 57, 80, 240, 250)}};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceBeqDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceBeqDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "beqEqOfEqEq"};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_1),((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 102, 212, 241, 77, 109, 37)}};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceBeqDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceBeqDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(241, 192, 105, 34, 163, 55, 67, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBneDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "bneTrueOfEqFalse"};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 18, 96, 112, 23, 126, 226, 206)}};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceBneDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceBneDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bneEqOfEqEq"};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value_aux_1),((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 158, 215, 107, 79, 237, 39, 137)}};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceBneDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceBneDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(187, 243, 98, 188, 219, 83, 246, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_le_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 38, 194, 84, 75, 182, 180, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_add_ge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 240, 107, 221, 21, 179, 249, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 232, 2, 112, 26, 243, 197, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_le_gt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(184, 68, 207, 87, 108, 168, 176, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_le_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 9, 215, 28, 195, 38, 233, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_le_add_ge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 197, 80, 96, 198, 252, 127, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceLeDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(46, 217, 224, 205, 36, 202, 222, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "sub_add_eq_comm"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 127, 24, 115, 7, 168, 162, 198)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "add_sub_le"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__2 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__2_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
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
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(3, 51, 84, 134, 180, 46, 92, 43)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__7 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "add_sub_add_ge"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__8 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__8_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(48, 27, 181, 35, 241, 165, 108, 235)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__9 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceSubDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(56, 43, 140, 205, 20, 127, 167, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(113, 66, 62, 145, 3, 197, 80, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getNatValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f___redArg___boxed(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Nat_fromExpr_x3f___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec_ref(v_e_8_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f(lean_object* v_e_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_getNatValue_x3f(v_e_15_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_fromExpr_x3f___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Nat_fromExpr_x3f(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg(lean_object* v_declName_37_, lean_object* v_arity_38_, lean_object* v_op_39_, lean_object* v_e_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_Expr_isAppOfArity(v_e_40_, v_declName_37_, v_arity_38_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec_ref(v_op_39_);
v___x_47_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___boxed(lean_object* v_declName_81_, lean_object* v_arity_82_, lean_object* v_op_83_, lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg(v_declName_81_, v_arity_82_, v_op_83_, v_e_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_e_84_);
lean_dec(v_declName_81_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary(lean_object* v_declName_91_, lean_object* v_arity_92_, lean_object* v_op_93_, lean_object* v_e_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Lean_Expr_isAppOfArity(v_e_94_, v_declName_91_, v_arity_92_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec_ref(v_op_93_);
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___boxed(lean_object* v_declName_138_, lean_object* v_arity_139_, lean_object* v_op_140_, lean_object* v_e_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary(v_declName_138_, v_arity_139_, v_op_140_, v_e_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___redArg(lean_object* v_declName_151_, lean_object* v_arity_152_, lean_object* v_op_153_, lean_object* v_e_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_Expr_isAppOfArity(v_e_154_, v_declName_151_, v_arity_152_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec_ref(v_op_153_);
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_166_, 1);
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
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___redArg___boxed(lean_object* v_declName_216_, lean_object* v_arity_217_, lean_object* v_op_218_, lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___redArg(v_declName_216_, v_arity_217_, v_op_218_, v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec_ref(v_e_219_);
lean_dec(v_declName_216_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin(lean_object* v_declName_226_, lean_object* v_arity_227_, lean_object* v_op_228_, lean_object* v_e_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_Expr_isAppOfArity(v_e_229_, v_declName_226_, v_arity_227_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v_op_228_);
v___x_239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_244_, 1);
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
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin___boxed(lean_object* v_declName_294_, lean_object* v_arity_295_, lean_object* v_op_296_, lean_object* v_e_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBin(v_declName_294_, v_arity_295_, v_op_296_, v_e_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg(lean_object* v_declName_309_, lean_object* v_arity_310_, lean_object* v_op_311_, lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Lean_Expr_isAppOfArity(v_e_312_, v_declName_309_, v_arity_310_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_e_312_);
lean_dec_ref(v_op_311_);
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
lean_dec_ref_known(v_a_324_, 1);
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
lean_dec_ref_known(v_a_331_, 1);
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
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___boxed(lean_object* v_declName_365_, lean_object* v_arity_366_, lean_object* v_op_367_, lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg(v_declName_365_, v_arity_366_, v_op_367_, v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_declName_365_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred(lean_object* v_declName_375_, lean_object* v_arity_376_, lean_object* v_op_377_, lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_Expr_isAppOfArity(v_e_378_, v_declName_375_, v_arity_376_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v_e_378_);
lean_dec_ref(v_op_377_);
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
lean_dec_ref_known(v_a_393_, 1);
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
lean_dec_ref_known(v_a_400_, 1);
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
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___boxed(lean_object* v_declName_434_, lean_object* v_arity_435_, lean_object* v_op_436_, lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred(v_declName_434_, v_arity_435_, v_op_436_, v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__2));
v___x_454_ = l_Lean_mkConst(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__5));
v___x_461_ = l_Lean_mkConst(v___x_460_, v___x_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg(lean_object* v_declName_462_, lean_object* v_arity_463_, lean_object* v_op_464_, lean_object* v_e_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Lean_Expr_isAppOfArity(v_e_465_, v_declName_462_, v_arity_463_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v_op_464_);
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_487_, 1);
v___x_500_ = lean_apply_2(v_op_464_, v_val_481_, v_val_499_);
v___x_501_ = lean_unbox(v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_492_ = v___x_502_;
goto v___jp_491_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
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
v___x_504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___boxed(lean_object* v_declName_531_, lean_object* v_arity_532_, lean_object* v_op_533_, lean_object* v_e_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg(v_declName_531_, v_arity_532_, v_op_533_, v_e_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_e_534_);
lean_dec(v_declName_531_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred(lean_object* v_declName_541_, lean_object* v_arity_542_, lean_object* v_op_543_, lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Expr_isAppOfArity(v_e_544_, v_declName_541_, v_arity_542_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_op_543_);
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_569_, 1);
v___x_582_ = lean_apply_2(v_op_543_, v_val_563_, v_val_581_);
v___x_583_ = lean_unbox(v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_574_ = v___x_584_;
goto v___jp_573_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
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
v___x_586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___boxed(lean_object* v_declName_613_, lean_object* v_arity_614_, lean_object* v_op_615_, lean_object* v_e_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred(v_declName_613_, v_arity_614_, v_op_615_, v_e_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
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
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_));
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_));
v___x_717_ = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
v___x_718_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_715_, v___x_716_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20____boxed(lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_();
return v_res_720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_));
v___x_725_ = 1;
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_);
v___x_727_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_724_, v___x_725_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22____boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_();
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_));
v___x_732_ = 1;
v___x_733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_);
v___x_734_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_731_, v___x_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_24____boxed(lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_24_();
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLog2___redArg(lean_object* v_e_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = ((lean_object*)(l_Nat_reduceLog2___redArg___closed__1));
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = l_Lean_Expr_isAppOfArity(v_e_741_, v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = l_Lean_Expr_appArg_x21(v_e_741_);
v___x_753_ = l_Lean_Meta_getNatValue_x3f(v___x_752_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec_ref(v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_775_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_775_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_775_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_775_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
if (lean_obj_tag(v_a_754_) == 1)
{
lean_object* v_val_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_770_; 
v_val_758_ = lean_ctor_get(v_a_754_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_a_754_);
if (v_isSharedCheck_770_ == 0)
{
v___x_760_ = v_a_754_;
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_val_758_);
lean_dec(v_a_754_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_762_ = lean_nat_log2(v_val_758_);
lean_dec(v_val_758_);
v___x_763_ = l_Lean_mkNatLit(v___x_762_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 0);
lean_ctor_set(v___x_760_, 0, v___x_763_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_765_);
v___x_767_ = v___x_756_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
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
else
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v_a_754_);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_771_);
v___x_773_ = v___x_756_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_a_776_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_753_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_753_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLog2___redArg___boxed(lean_object* v_e_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Nat_reduceLog2___redArg(v_e_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec_ref(v_e_784_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLog2(lean_object* v_e_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Nat_reduceLog2___redArg(v_e_791_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLog2___boxed(lean_object* v_e_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Nat_reduceLog2(v_e_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_e_801_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_));
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_));
v___x_827_ = lean_alloc_closure((void*)(l_Nat_reduceLog2___boxed), 9, 0);
v___x_828_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_825_, v___x_826_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20____boxed(lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_();
return v_res_830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_alloc_closure((void*)(l_Nat_reduceLog2___boxed), 9, 0);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_));
v___x_835_ = 1;
v___x_836_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_);
v___x_837_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_834_, v___x_835_, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22____boxed(lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_));
v___x_842_ = 1;
v___x_843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_);
v___x_844_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_841_, v___x_842_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_24____boxed(lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_24_();
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg(lean_object* v_e_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_859_ = lean_unsigned_to_nat(6u);
v___x_860_ = l_Lean_Expr_isAppOfArity(v_e_852_, v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = l_Lean_Expr_appFn_x21(v_e_852_);
v___x_864_ = l_Lean_Expr_appArg_x21(v___x_863_);
lean_dec_ref(v___x_863_);
v___x_865_ = l_Lean_Meta_getNatValue_x3f(v___x_864_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec_ref(v___x_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_907_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_907_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_907_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_907_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
if (lean_obj_tag(v_a_866_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_del_object(v___x_868_);
v_val_870_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_val_870_);
lean_dec_ref_known(v_a_866_, 1);
v___x_871_ = l_Lean_Expr_appArg_x21(v_e_852_);
v___x_872_ = l_Lean_Meta_getNatValue_x3f(v___x_871_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec_ref(v___x_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_894_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_894_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_894_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_894_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
if (lean_obj_tag(v_a_873_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_889_; 
v_val_877_ = lean_ctor_get(v_a_873_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_889_ == 0)
{
v___x_879_ = v_a_873_;
v_isShared_880_ = v_isSharedCheck_889_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v_a_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_889_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = lean_nat_add(v_val_870_, v_val_877_);
lean_dec(v_val_877_);
lean_dec(v_val_870_);
v___x_882_ = l_Lean_mkNatLit(v___x_881_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 0);
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_884_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
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
else
{
lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec(v_a_873_);
lean_dec(v_val_870_);
v___x_890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_890_);
v___x_892_ = v___x_875_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_val_870_);
v_a_895_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_872_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_872_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_905_; 
lean_dec(v_a_866_);
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_903_);
v___x_905_ = v___x_868_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
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
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_865_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_865_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg___boxed(lean_object* v_e_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Nat_reduceAdd___redArg(v_e_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec_ref(v_e_916_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object* v_e_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Nat_reduceAdd___redArg(v_e_923_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object* v_e_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Nat_reduceAdd(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_e_933_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_970_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_971_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_968_, v___x_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26____boxed(lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_();
return v_res_973_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_978_ = 1;
v___x_979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_);
v___x_980_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_977_, v___x_978_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28____boxed(lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_();
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_985_ = 1;
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_);
v___x_987_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_984_, v___x_985_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30____boxed(lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_();
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg(lean_object* v_e_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = ((lean_object*)(l_Nat_reduceMul___redArg___closed__2));
v___x_1002_ = lean_unsigned_to_nat(6u);
v___x_1003_ = l_Lean_Expr_isAppOfArity(v_e_995_, v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = l_Lean_Expr_appFn_x21(v_e_995_);
v___x_1007_ = l_Lean_Expr_appArg_x21(v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = l_Lean_Meta_getNatValue_x3f(v___x_1007_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec_ref(v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1050_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1050_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1050_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_del_object(v___x_1011_);
v_val_1013_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_a_1009_, 1);
v___x_1014_ = l_Lean_Expr_appArg_x21(v_e_995_);
v___x_1015_ = l_Lean_Meta_getNatValue_x3f(v___x_1014_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec_ref(v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1037_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1037_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1037_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
if (lean_obj_tag(v_a_1016_) == 1)
{
lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1032_; 
v_val_1020_ = lean_ctor_get(v_a_1016_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_a_1016_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1022_ = v_a_1016_;
v_isShared_1023_ = v_isSharedCheck_1032_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_dec(v_a_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1032_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = lean_nat_mul(v_val_1013_, v_val_1020_);
lean_dec(v_val_1020_);
lean_dec(v_val_1013_);
v___x_1025_ = l_Lean_mkNatLit(v___x_1024_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1027_);
v___x_1029_ = v___x_1018_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
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
else
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec(v_a_1016_);
lean_dec(v_val_1013_);
v___x_1033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1033_);
v___x_1035_ = v___x_1018_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_val_1013_);
v_a_1038_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1015_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1015_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v_a_1009_);
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1046_);
v___x_1048_ = v___x_1011_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1008_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1008_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg___boxed(lean_object* v_e_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Nat_reduceMul___redArg(v_e_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_e_1059_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Nat_reduceMul___redArg(v_e_1066_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object* v_e_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Nat_reduceMul(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_e_1076_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_1108_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_1109_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1106_, v___x_1107_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26____boxed(lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_();
return v_res_1111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_1116_ = 1;
v___x_1117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_);
v___x_1118_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1115_, v___x_1116_, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28____boxed(lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_();
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_1123_ = 1;
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_);
v___x_1125_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1122_, v___x_1123_, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30____boxed(lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_();
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg(lean_object* v_e_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_1140_ = lean_unsigned_to_nat(6u);
v___x_1141_ = l_Lean_Expr_isAppOfArity(v_e_1133_, v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = l_Lean_Expr_appFn_x21(v_e_1133_);
v___x_1145_ = l_Lean_Expr_appArg_x21(v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = l_Lean_Meta_getNatValue_x3f(v___x_1145_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec_ref(v___x_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1188_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1188_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1188_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
if (lean_obj_tag(v_a_1147_) == 1)
{
lean_object* v_val_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_del_object(v___x_1149_);
v_val_1151_ = lean_ctor_get(v_a_1147_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v_a_1147_, 1);
v___x_1152_ = l_Lean_Expr_appArg_x21(v_e_1133_);
v___x_1153_ = l_Lean_Meta_getNatValue_x3f(v___x_1152_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec_ref(v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1175_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1175_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1175_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
if (lean_obj_tag(v_a_1154_) == 1)
{
lean_object* v_val_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
v_val_1158_ = lean_ctor_get(v_a_1154_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_1154_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v_a_1154_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_val_1158_);
lean_dec(v_a_1154_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = lean_nat_sub(v_val_1151_, v_val_1158_);
lean_dec(v_val_1158_);
lean_dec(v_val_1151_);
v___x_1163_ = l_Lean_mkNatLit(v___x_1162_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1163_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1165_);
v___x_1167_ = v___x_1156_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec(v_a_1154_);
lean_dec(v_val_1151_);
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1171_);
v___x_1173_ = v___x_1156_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_val_1151_);
v_a_1176_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1153_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1153_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
lean_dec(v_a_1147_);
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1184_);
v___x_1186_ = v___x_1149_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_a_1189_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1146_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1146_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg___boxed(lean_object* v_e_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Nat_reduceSub___redArg(v_e_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec_ref(v_e_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object* v_e_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Nat_reduceSub___redArg(v_e_1204_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object* v_e_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Nat_reduceSub(v_e_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_e_1214_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1246_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1247_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1244_, v___x_1245_, v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26____boxed(lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_();
return v_res_1249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1254_ = 1;
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_);
v___x_1256_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1253_, v___x_1254_, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28____boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_();
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1261_ = 1;
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_);
v___x_1263_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1260_, v___x_1261_, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30____boxed(lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_();
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg(lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = ((lean_object*)(l_Nat_reduceDiv___redArg___closed__2));
v___x_1278_ = lean_unsigned_to_nat(6u);
v___x_1279_ = l_Lean_Expr_isAppOfArity(v_e_1271_, v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = l_Lean_Expr_appFn_x21(v_e_1271_);
v___x_1283_ = l_Lean_Expr_appArg_x21(v___x_1282_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = l_Lean_Meta_getNatValue_x3f(v___x_1283_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec_ref(v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1326_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1326_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1326_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
if (lean_obj_tag(v_a_1285_) == 1)
{
lean_object* v_val_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_del_object(v___x_1287_);
v_val_1289_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v_a_1285_, 1);
v___x_1290_ = l_Lean_Expr_appArg_x21(v_e_1271_);
v___x_1291_ = l_Lean_Meta_getNatValue_x3f(v___x_1290_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec_ref(v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1313_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1313_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1313_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
if (lean_obj_tag(v_a_1292_) == 1)
{
lean_object* v_val_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1308_; 
v_val_1296_ = lean_ctor_get(v_a_1292_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_a_1292_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1298_ = v_a_1292_;
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_val_1296_);
lean_dec(v_a_1292_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1300_ = lean_nat_div(v_val_1289_, v_val_1296_);
lean_dec(v_val_1296_);
lean_dec(v_val_1289_);
v___x_1301_ = l_Lean_mkNatLit(v___x_1300_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1301_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1303_);
v___x_1305_ = v___x_1294_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v_a_1292_);
lean_dec(v_val_1289_);
v___x_1309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1309_);
v___x_1311_ = v___x_1294_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_val_1289_);
v_a_1314_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1291_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1291_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_a_1285_);
v___x_1322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1322_);
v___x_1324_ = v___x_1287_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1284_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1284_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg___boxed(lean_object* v_e_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Nat_reduceDiv___redArg(v_e_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec_ref(v_e_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object* v_e_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Nat_reduceDiv___redArg(v_e_1342_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object* v_e_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Nat_reduceDiv(v_e_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_e_1352_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1384_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1385_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1382_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26____boxed(lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_();
return v_res_1387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1392_ = 1;
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_);
v___x_1394_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1391_, v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28____boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_();
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1399_ = 1;
v___x_1400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_);
v___x_1401_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1398_, v___x_1399_, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30____boxed(lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_();
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg(lean_object* v_e_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1415_ = ((lean_object*)(l_Nat_reduceMod___redArg___closed__2));
v___x_1416_ = lean_unsigned_to_nat(6u);
v___x_1417_ = l_Lean_Expr_isAppOfArity(v_e_1409_, v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = l_Lean_Expr_appFn_x21(v_e_1409_);
v___x_1421_ = l_Lean_Expr_appArg_x21(v___x_1420_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = l_Lean_Meta_getNatValue_x3f(v___x_1421_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec_ref(v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1464_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1464_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1464_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_del_object(v___x_1425_);
v_val_1427_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_val_1427_);
lean_dec_ref_known(v_a_1423_, 1);
v___x_1428_ = l_Lean_Expr_appArg_x21(v_e_1409_);
v___x_1429_ = l_Lean_Meta_getNatValue_x3f(v___x_1428_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec_ref(v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1451_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1451_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1451_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
if (lean_obj_tag(v_a_1430_) == 1)
{
lean_object* v_val_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1446_; 
v_val_1434_ = lean_ctor_get(v_a_1430_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_a_1430_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1436_ = v_a_1430_;
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_val_1434_);
lean_dec(v_a_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1438_ = lean_nat_mod(v_val_1427_, v_val_1434_);
lean_dec(v_val_1434_);
lean_dec(v_val_1427_);
v___x_1439_ = l_Lean_mkNatLit(v___x_1438_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1441_);
v___x_1443_ = v___x_1432_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_dec(v_a_1430_);
lean_dec(v_val_1427_);
v___x_1447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1447_);
v___x_1449_ = v___x_1432_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_val_1427_);
v_a_1452_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1429_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1429_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec(v_a_1423_);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1460_);
v___x_1462_ = v___x_1425_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1422_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1422_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg___boxed(lean_object* v_e_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Nat_reduceMod___redArg(v_e_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec_ref(v_e_1473_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Nat_reduceMod___redArg(v_e_1480_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Nat_reduceMod(v_e_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_e_1490_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1522_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1523_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1520_, v___x_1521_, v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26____boxed(lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_();
return v_res_1525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1530_ = 1;
v___x_1531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_);
v___x_1532_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1529_, v___x_1530_, v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28____boxed(lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_();
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1537_ = 1;
v___x_1538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_);
v___x_1539_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1536_, v___x_1537_, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30____boxed(lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_();
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg(lean_object* v_e_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = l_Lean_Expr_cleanupAnnotations(v_e_1547_);
v___x_1558_ = l_Lean_Expr_isApp(v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec_ref(v___x_1557_);
goto v___jp_1554_;
}
else
{
lean_object* v_arg_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_arg_1559_ = lean_ctor_get(v___x_1557_, 1);
lean_inc_ref(v_arg_1559_);
v___x_1560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1557_);
v___x_1561_ = l_Lean_Expr_isApp(v___x_1560_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_arg_1559_);
goto v___jp_1554_;
}
else
{
lean_object* v_arg_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_arg_1562_ = lean_ctor_get(v___x_1560_, 1);
lean_inc_ref(v_arg_1562_);
v___x_1563_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1560_);
v___x_1564_ = l_Lean_Expr_isApp(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v___x_1563_);
lean_dec_ref(v_arg_1562_);
lean_dec_ref(v_arg_1559_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1563_);
v___x_1566_ = l_Lean_Expr_isApp(v___x_1565_);
if (v___x_1566_ == 0)
{
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_arg_1562_);
lean_dec_ref(v_arg_1559_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1565_);
v___x_1568_ = l_Lean_Expr_isApp(v___x_1567_);
if (v___x_1568_ == 0)
{
lean_dec_ref(v___x_1567_);
lean_dec_ref(v_arg_1562_);
lean_dec_ref(v_arg_1559_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1567_);
v___x_1570_ = l_Lean_Expr_isApp(v___x_1569_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_arg_1562_);
lean_dec_ref(v_arg_1559_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1569_);
v___x_1572_ = ((lean_object*)(l_Nat_reducePow___redArg___closed__2));
v___x_1573_ = l_Lean_Expr_isConstOf(v___x_1571_, v___x_1572_);
lean_dec_ref(v___x_1571_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v_arg_1562_);
lean_dec_ref(v_arg_1559_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_getNatValue_x3f(v_arg_1562_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec_ref(v_arg_1562_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1636_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1636_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1636_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
if (lean_obj_tag(v_a_1575_) == 1)
{
lean_object* v_val_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1577_);
v_val_1579_ = lean_ctor_get(v_a_1575_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_a_1575_, 1);
v___x_1580_ = l_Lean_Meta_getNatValue_x3f(v_arg_1559_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec_ref(v_arg_1559_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1623_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1623_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1623_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_config_1585_; lean_object* v_val_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1618_; 
lean_del_object(v___x_1583_);
v_config_1585_ = lean_ctor_get(v_a_1548_, 0);
v_val_1586_ = lean_ctor_get(v_a_1581_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_a_1581_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1588_ = v_a_1581_;
v_isShared_1589_ = v_isSharedCheck_1618_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_val_1586_);
lean_dec(v_a_1581_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1618_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
uint8_t v_warnExponents_1590_; lean_object* v___x_1591_; 
v_warnExponents_1590_ = lean_ctor_get_uint8(v_config_1585_, sizeof(void*)*3 + 25);
lean_inc(v_val_1586_);
v___x_1591_ = l_Lean_checkExponent(v_val_1586_, v_warnExponents_1590_, v_a_1551_, v_a_1552_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1609_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1609_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1609_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_unbox(v_a_1592_);
lean_dec(v_a_1592_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_del_object(v___x_1588_);
lean_dec(v_val_1586_);
lean_dec(v_val_1579_);
v___x_1597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = lean_nat_pow(v_val_1579_, v_val_1586_);
lean_dec(v_val_1586_);
lean_dec(v_val_1579_);
v___x_1602_ = l_Lean_mkNatLit(v___x_1601_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1602_);
v___x_1604_ = v___x_1588_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1604_);
v___x_1606_ = v___x_1594_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1588_);
lean_dec(v_val_1586_);
lean_dec(v_val_1579_);
v_a_1610_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1591_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1591_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_dec(v_a_1581_);
lean_dec(v_val_1579_);
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1619_);
v___x_1621_ = v___x_1583_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_val_1579_);
v_a_1624_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1580_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1580_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_dec(v_a_1575_);
lean_dec_ref(v_arg_1559_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1632_);
v___x_1634_ = v___x_1577_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_arg_1559_);
v_a_1637_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1574_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1574_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
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
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg___boxed(lean_object* v_e_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Nat_reducePow___redArg(v_e_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec_ref(v_a_1646_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object* v_e_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Nat_reducePow___redArg(v_e_1653_, v_a_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object* v_e_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Nat_reducePow(v_e_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1695_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1696_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1693_, v___x_1694_, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26____boxed(lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_();
return v_res_1698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1703_ = 1;
v___x_1704_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_);
v___x_1705_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1702_, v___x_1703_, v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28____boxed(lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_();
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1710_ = 1;
v___x_1711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_);
v___x_1712_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1709_, v___x_1710_, v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30____boxed(lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_();
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePowMod___redArg(lean_object* v_e_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = l_Lean_Expr_cleanupAnnotations(v_e_1719_);
v___x_1730_ = l_Lean_Expr_isApp(v___x_1729_);
if (v___x_1730_ == 0)
{
lean_dec_ref(v___x_1729_);
goto v___jp_1726_;
}
else
{
lean_object* v_arg_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_arg_1731_ = lean_ctor_get(v___x_1729_, 1);
lean_inc_ref(v_arg_1731_);
v___x_1732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1729_);
v___x_1733_ = l_Lean_Expr_isApp(v___x_1732_);
if (v___x_1733_ == 0)
{
lean_dec_ref(v___x_1732_);
lean_dec_ref(v_arg_1731_);
goto v___jp_1726_;
}
else
{
lean_object* v_arg_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v_arg_1734_ = lean_ctor_get(v___x_1732_, 1);
lean_inc_ref(v_arg_1734_);
v___x_1735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1732_);
v___x_1736_ = l_Lean_Expr_isApp(v___x_1735_);
if (v___x_1736_ == 0)
{
lean_dec_ref(v___x_1735_);
lean_dec_ref(v_arg_1734_);
lean_dec_ref(v_arg_1731_);
goto v___jp_1726_;
}
else
{
lean_object* v_arg_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_arg_1737_ = lean_ctor_get(v___x_1735_, 1);
lean_inc_ref(v_arg_1737_);
v___x_1738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1735_);
v___x_1739_ = ((lean_object*)(l_Nat_reducePowMod___redArg___closed__1));
v___x_1740_ = l_Lean_Expr_isConstOf(v___x_1738_, v___x_1739_);
lean_dec_ref(v___x_1738_);
if (v___x_1740_ == 0)
{
lean_dec_ref(v_arg_1737_);
lean_dec_ref(v_arg_1734_);
lean_dec_ref(v_arg_1731_);
goto v___jp_1726_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_getNatValue_x3f(v_arg_1737_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec_ref(v_arg_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1825_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1825_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1825_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
if (lean_obj_tag(v_a_1742_) == 1)
{
lean_object* v_val_1746_; lean_object* v___x_1747_; 
lean_del_object(v___x_1744_);
v_val_1746_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v_a_1742_, 1);
v___x_1747_ = l_Lean_Meta_getNatValue_x3f(v_arg_1734_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec_ref(v_arg_1734_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1812_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1812_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1812_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
if (lean_obj_tag(v_a_1748_) == 1)
{
lean_object* v_val_1752_; lean_object* v___x_1753_; 
lean_del_object(v___x_1750_);
v_val_1752_ = lean_ctor_get(v_a_1748_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v_a_1748_, 1);
v___x_1753_ = l_Lean_Meta_getNatValue_x3f(v_arg_1731_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec_ref(v_arg_1731_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1799_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1799_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1799_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
if (lean_obj_tag(v_a_1754_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1794_; 
v_val_1758_ = lean_ctor_get(v_a_1754_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1760_ = v_a_1754_;
v_isShared_1761_ = v_isSharedCheck_1794_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v_a_1754_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1794_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_nat_dec_eq(v_val_1758_, v___x_1771_);
if (v___x_1772_ == 0)
{
goto v___jp_1762_;
}
else
{
lean_object* v_config_1773_; uint8_t v_warnExponents_1774_; lean_object* v___x_1775_; 
v_config_1773_ = lean_ctor_get(v_a_1720_, 0);
v_warnExponents_1774_ = lean_ctor_get_uint8(v_config_1773_, sizeof(void*)*3 + 25);
lean_inc(v_val_1752_);
v___x_1775_ = l_Lean_checkExponent(v_val_1752_, v_warnExponents_1774_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_unbox(v_a_1776_);
lean_dec(v_a_1776_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_del_object(v___x_1760_);
lean_dec(v_val_1758_);
lean_del_object(v___x_1756_);
lean_dec(v_val_1752_);
lean_dec(v_val_1746_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1783_ = v___x_1778_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
else
{
lean_del_object(v___x_1778_);
goto v___jp_1762_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_del_object(v___x_1760_);
lean_dec(v_val_1758_);
lean_del_object(v___x_1756_);
lean_dec(v_val_1752_);
lean_dec(v_val_1746_);
v_a_1786_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1775_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1775_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
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
v___jp_1762_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = lean_nat_powmod(v_val_1746_, v_val_1752_, v_val_1758_);
lean_dec(v_val_1758_);
lean_dec(v_val_1752_);
lean_dec(v_val_1746_);
v___x_1764_ = l_Lean_mkNatLit(v___x_1763_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1764_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1766_);
v___x_1768_ = v___x_1756_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec(v_a_1754_);
lean_dec(v_val_1752_);
lean_dec(v_val_1746_);
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1795_);
v___x_1797_ = v___x_1756_;
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
lean_dec(v_val_1752_);
lean_dec(v_val_1746_);
v_a_1800_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1753_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1753_);
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
lean_dec(v_a_1748_);
lean_dec(v_val_1746_);
lean_dec_ref(v_arg_1731_);
v___x_1808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1808_);
v___x_1810_ = v___x_1750_;
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
lean_dec(v_val_1746_);
lean_dec_ref(v_arg_1731_);
v_a_1813_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1747_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1747_);
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
else
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec(v_a_1742_);
lean_dec_ref(v_arg_1734_);
lean_dec_ref(v_arg_1731_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1821_);
v___x_1823_ = v___x_1744_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_arg_1734_);
lean_dec_ref(v_arg_1731_);
v_a_1826_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1741_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1741_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
}
v___jp_1726_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePowMod___redArg___boxed(lean_object* v_e_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Nat_reducePowMod___redArg(v_e_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePowMod(lean_object* v_e_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Nat_reducePowMod___redArg(v_e_1842_, v_a_1844_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePowMod___boxed(lean_object* v_e_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Nat_reducePowMod(v_e_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_));
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_));
v___x_1880_ = lean_alloc_closure((void*)(l_Nat_reducePowMod___boxed), 9, 0);
v___x_1881_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1878_, v___x_1879_, v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22____boxed(lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_();
return v_res_1883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_alloc_closure((void*)(l_Nat_reducePowMod___boxed), 9, 0);
v___x_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_));
v___x_1888_ = 1;
v___x_1889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_);
v___x_1890_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1887_, v___x_1888_, v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24____boxed(lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_();
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_));
v___x_1895_ = 1;
v___x_1896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_);
v___x_1897_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1894_, v___x_1895_, v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_26____boxed(lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_26_();
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg(lean_object* v_e_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1911_ = ((lean_object*)(l_Nat_reduceAnd___redArg___closed__2));
v___x_1912_ = lean_unsigned_to_nat(6u);
v___x_1913_ = l_Lean_Expr_isAppOfArity(v_e_1905_, v___x_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = l_Lean_Expr_appFn_x21(v_e_1905_);
v___x_1917_ = l_Lean_Expr_appArg_x21(v___x_1916_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = l_Lean_Meta_getNatValue_x3f(v___x_1917_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec_ref(v___x_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1960_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1960_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1960_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
if (lean_obj_tag(v_a_1919_) == 1)
{
lean_object* v_val_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_del_object(v___x_1921_);
v_val_1923_ = lean_ctor_get(v_a_1919_, 0);
lean_inc(v_val_1923_);
lean_dec_ref_known(v_a_1919_, 1);
v___x_1924_ = l_Lean_Expr_appArg_x21(v_e_1905_);
v___x_1925_ = l_Lean_Meta_getNatValue_x3f(v___x_1924_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec_ref(v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1947_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
if (lean_obj_tag(v_a_1926_) == 1)
{
lean_object* v_val_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1942_; 
v_val_1930_ = lean_ctor_get(v_a_1926_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_a_1926_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1932_ = v_a_1926_;
v_isShared_1933_ = v_isSharedCheck_1942_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_val_1930_);
lean_dec(v_a_1926_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1942_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1934_ = lean_nat_land(v_val_1923_, v_val_1930_);
lean_dec(v_val_1930_);
lean_dec(v_val_1923_);
v___x_1935_ = l_Lean_mkNatLit(v___x_1934_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1939_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1937_);
v___x_1939_ = v___x_1928_;
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
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec(v_a_1926_);
lean_dec(v_val_1923_);
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1943_);
v___x_1945_ = v___x_1928_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_val_1923_);
v_a_1948_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1925_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1925_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
lean_dec(v_a_1919_);
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1956_);
v___x_1958_ = v___x_1921_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1961_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1918_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1918_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg___boxed(lean_object* v_e_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Nat_reduceAnd___redArg(v_e_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_e_1969_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object* v_e_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Nat_reduceAnd___redArg(v_e_1976_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object* v_e_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Nat_reduceAnd(v_e_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_e_1986_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_2018_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_2019_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2016_, v___x_2017_, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26____boxed(lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_();
return v_res_2021_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_2026_ = 1;
v___x_2027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_);
v___x_2028_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2025_, v___x_2026_, v___x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28____boxed(lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_();
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_2033_ = 1;
v___x_2034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_);
v___x_2035_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2032_, v___x_2033_, v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30____boxed(lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_();
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg(lean_object* v_e_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2049_ = ((lean_object*)(l_Nat_reduceXor___redArg___closed__2));
v___x_2050_ = lean_unsigned_to_nat(6u);
v___x_2051_ = l_Lean_Expr_isAppOfArity(v_e_2043_, v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_Expr_appFn_x21(v_e_2043_);
v___x_2055_ = l_Lean_Expr_appArg_x21(v___x_2054_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = l_Lean_Meta_getNatValue_x3f(v___x_2055_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec_ref(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2098_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2098_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2098_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
if (lean_obj_tag(v_a_2057_) == 1)
{
lean_object* v_val_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_del_object(v___x_2059_);
v_val_2061_ = lean_ctor_get(v_a_2057_, 0);
lean_inc(v_val_2061_);
lean_dec_ref_known(v_a_2057_, 1);
v___x_2062_ = l_Lean_Expr_appArg_x21(v_e_2043_);
v___x_2063_ = l_Lean_Meta_getNatValue_x3f(v___x_2062_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec_ref(v___x_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2085_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2085_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2085_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
if (lean_obj_tag(v_a_2064_) == 1)
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2080_; 
v_val_2068_ = lean_ctor_get(v_a_2064_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2064_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2070_ = v_a_2064_;
v_isShared_2071_ = v_isSharedCheck_2080_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v_a_2064_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2080_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2072_ = lean_nat_lxor(v_val_2061_, v_val_2068_);
lean_dec(v_val_2068_);
lean_dec(v_val_2061_);
v___x_2073_ = l_Lean_mkNatLit(v___x_2072_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2073_);
v___x_2075_ = v___x_2070_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2075_);
v___x_2077_ = v___x_2066_;
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
lean_object* v___x_2081_; lean_object* v___x_2083_; 
lean_dec(v_a_2064_);
lean_dec(v_val_2061_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2081_);
v___x_2083_ = v___x_2066_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_val_2061_);
v_a_2086_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2063_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2063_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_dec(v_a_2057_);
v___x_2094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2094_);
v___x_2096_ = v___x_2059_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2056_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2056_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg___boxed(lean_object* v_e_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Nat_reduceXor___redArg(v_e_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec_ref(v_e_2107_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Nat_reduceXor___redArg(v_e_2114_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object* v_e_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Nat_reduceXor(v_e_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_e_2124_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_2155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_2156_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_2157_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2154_, v___x_2155_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26____boxed(lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_();
return v_res_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_2164_ = 1;
v___x_2165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_);
v___x_2166_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2163_, v___x_2164_, v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28____boxed(lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_();
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_2171_ = 1;
v___x_2172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_);
v___x_2173_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2170_, v___x_2171_, v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30____boxed(lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_();
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg(lean_object* v_e_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2187_ = ((lean_object*)(l_Nat_reduceOr___redArg___closed__2));
v___x_2188_ = lean_unsigned_to_nat(6u);
v___x_2189_ = l_Lean_Expr_isAppOfArity(v_e_2181_, v___x_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = l_Lean_Expr_appFn_x21(v_e_2181_);
v___x_2193_ = l_Lean_Expr_appArg_x21(v___x_2192_);
lean_dec_ref(v___x_2192_);
v___x_2194_ = l_Lean_Meta_getNatValue_x3f(v___x_2193_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
lean_dec_ref(v___x_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2236_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2236_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2236_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_del_object(v___x_2197_);
v_val_2199_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2200_ = l_Lean_Expr_appArg_x21(v_e_2181_);
v___x_2201_ = l_Lean_Meta_getNatValue_x3f(v___x_2200_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
lean_dec_ref(v___x_2200_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2223_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2223_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2223_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
if (lean_obj_tag(v_a_2202_) == 1)
{
lean_object* v_val_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2218_; 
v_val_2206_ = lean_ctor_get(v_a_2202_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2208_ = v_a_2202_;
v_isShared_2209_ = v_isSharedCheck_2218_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_val_2206_);
lean_dec(v_a_2202_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2218_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_nat_lor(v_val_2199_, v_val_2206_);
lean_dec(v_val_2206_);
lean_dec(v_val_2199_);
v___x_2211_ = l_Lean_mkNatLit(v___x_2210_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2213_);
v___x_2215_ = v___x_2204_;
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
lean_object* v___x_2219_; lean_object* v___x_2221_; 
lean_dec(v_a_2202_);
lean_dec(v_val_2199_);
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2219_);
v___x_2221_ = v___x_2204_;
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
lean_dec(v_val_2199_);
v_a_2224_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2201_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2201_);
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
lean_dec(v_a_2195_);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2232_);
v___x_2234_ = v___x_2197_;
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
v_a_2237_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2194_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2194_);
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
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg___boxed(lean_object* v_e_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Nat_reduceOr___redArg(v_e_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec_ref(v_e_2245_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object* v_e_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Nat_reduceOr___redArg(v_e_2252_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Nat_reduceOr(v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_e_2262_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_2293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_2294_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2295_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2292_, v___x_2293_, v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26____boxed(lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_();
return v_res_2297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_2302_ = 1;
v___x_2303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_);
v___x_2304_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2301_, v___x_2302_, v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28____boxed(lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_();
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_2309_ = 1;
v___x_2310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_);
v___x_2311_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2308_, v___x_2309_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30____boxed(lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_();
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg(lean_object* v_e_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2325_ = ((lean_object*)(l_Nat_reduceShiftLeft___redArg___closed__2));
v___x_2326_ = lean_unsigned_to_nat(6u);
v___x_2327_ = l_Lean_Expr_isAppOfArity(v_e_2319_, v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = l_Lean_Expr_appFn_x21(v_e_2319_);
v___x_2331_ = l_Lean_Expr_appArg_x21(v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = l_Lean_Meta_getNatValue_x3f(v___x_2331_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec_ref(v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2374_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2374_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2374_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
if (lean_obj_tag(v_a_2333_) == 1)
{
lean_object* v_val_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_del_object(v___x_2335_);
v_val_2337_ = lean_ctor_get(v_a_2333_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v_a_2333_, 1);
v___x_2338_ = l_Lean_Expr_appArg_x21(v_e_2319_);
v___x_2339_ = l_Lean_Meta_getNatValue_x3f(v___x_2338_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec_ref(v___x_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2361_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2361_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2361_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
if (lean_obj_tag(v_a_2340_) == 1)
{
lean_object* v_val_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2356_; 
v_val_2344_ = lean_ctor_get(v_a_2340_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_a_2340_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2346_ = v_a_2340_;
v_isShared_2347_ = v_isSharedCheck_2356_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_val_2344_);
lean_dec(v_a_2340_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2356_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2348_ = lean_nat_shiftl(v_val_2337_, v_val_2344_);
lean_dec(v_val_2344_);
lean_dec(v_val_2337_);
v___x_2349_ = l_Lean_mkNatLit(v___x_2348_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2349_);
v___x_2351_ = v___x_2346_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2351_);
v___x_2353_ = v___x_2342_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_dec(v_a_2340_);
lean_dec(v_val_2337_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2357_);
v___x_2359_ = v___x_2342_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_val_2337_);
v_a_2362_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2339_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2339_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_dec(v_a_2333_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2370_);
v___x_2372_ = v___x_2335_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_a_2375_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2332_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2332_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg___boxed(lean_object* v_e_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Nat_reduceShiftLeft___redArg(v_e_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec_ref(v_e_2383_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object* v_e_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Nat_reduceShiftLeft___redArg(v_e_2390_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object* v_e_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Nat_reduceShiftLeft(v_e_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_e_2400_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2432_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2433_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2430_, v___x_2431_, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26____boxed(lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_();
return v_res_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2440_ = 1;
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_);
v___x_2442_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2439_, v___x_2440_, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28____boxed(lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_();
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2447_ = 1;
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_);
v___x_2449_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2446_, v___x_2447_, v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30____boxed(lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_();
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg(lean_object* v_e_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2463_ = ((lean_object*)(l_Nat_reduceShiftRight___redArg___closed__2));
v___x_2464_ = lean_unsigned_to_nat(6u);
v___x_2465_ = l_Lean_Expr_isAppOfArity(v_e_2457_, v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = l_Lean_Expr_appFn_x21(v_e_2457_);
v___x_2469_ = l_Lean_Expr_appArg_x21(v___x_2468_);
lean_dec_ref(v___x_2468_);
v___x_2470_ = l_Lean_Meta_getNatValue_x3f(v___x_2469_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v___x_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2512_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2512_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2512_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
if (lean_obj_tag(v_a_2471_) == 1)
{
lean_object* v_val_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_del_object(v___x_2473_);
v_val_2475_ = lean_ctor_get(v_a_2471_, 0);
lean_inc(v_val_2475_);
lean_dec_ref_known(v_a_2471_, 1);
v___x_2476_ = l_Lean_Expr_appArg_x21(v_e_2457_);
v___x_2477_ = l_Lean_Meta_getNatValue_x3f(v___x_2476_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v___x_2476_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2499_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2499_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2499_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
if (lean_obj_tag(v_a_2478_) == 1)
{
lean_object* v_val_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2494_; 
v_val_2482_ = lean_ctor_get(v_a_2478_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2478_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2484_ = v_a_2478_;
v_isShared_2485_ = v_isSharedCheck_2494_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_val_2482_);
lean_dec(v_a_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2494_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2486_ = lean_nat_shiftr(v_val_2475_, v_val_2482_);
lean_dec(v_val_2482_);
lean_dec(v_val_2475_);
v___x_2487_ = l_Lean_mkNatLit(v___x_2486_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set_tag(v___x_2484_, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2487_);
v___x_2489_ = v___x_2484_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2489_);
v___x_2491_ = v___x_2480_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
lean_dec(v_a_2478_);
lean_dec(v_val_2475_);
v___x_2495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2495_);
v___x_2497_ = v___x_2480_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_val_2475_);
v_a_2500_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2477_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2477_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_dec(v_a_2471_);
v___x_2508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2508_);
v___x_2510_ = v___x_2473_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v_a_2513_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2470_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2470_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg___boxed(lean_object* v_e_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Nat_reduceShiftRight___redArg(v_e_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec_ref(v_e_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object* v_e_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Nat_reduceShiftRight___redArg(v_e_2528_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object* v_e_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Nat_reduceShiftRight(v_e_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2538_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2570_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2571_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2568_, v___x_2569_, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26____boxed(lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_();
return v_res_2573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2578_ = 1;
v___x_2579_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_);
v___x_2580_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2577_, v___x_2578_, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28____boxed(lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_();
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2585_ = 1;
v___x_2586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_);
v___x_2587_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2584_, v___x_2585_, v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30____boxed(lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_();
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object* v_e_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2600_ = ((lean_object*)(l_Nat_reduceGcd___redArg___closed__1));
v___x_2601_ = lean_unsigned_to_nat(2u);
v___x_2602_ = l_Lean_Expr_isAppOfArity(v_e_2594_, v___x_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = l_Lean_Expr_appFn_x21(v_e_2594_);
v___x_2606_ = l_Lean_Expr_appArg_x21(v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2607_ = l_Lean_Meta_getNatValue_x3f(v___x_2606_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec_ref(v___x_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2649_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2649_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2649_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
if (lean_obj_tag(v_a_2608_) == 1)
{
lean_object* v_val_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_del_object(v___x_2610_);
v_val_2612_ = lean_ctor_get(v_a_2608_, 0);
lean_inc(v_val_2612_);
lean_dec_ref_known(v_a_2608_, 1);
v___x_2613_ = l_Lean_Expr_appArg_x21(v_e_2594_);
v___x_2614_ = l_Lean_Meta_getNatValue_x3f(v___x_2613_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec_ref(v___x_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2636_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2636_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2636_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
if (lean_obj_tag(v_a_2615_) == 1)
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2631_; 
v_val_2619_ = lean_ctor_get(v_a_2615_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_a_2615_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2621_ = v_a_2615_;
v_isShared_2622_ = v_isSharedCheck_2631_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v_a_2615_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2631_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = lean_nat_gcd(v_val_2612_, v_val_2619_);
lean_dec(v_val_2619_);
lean_dec(v_val_2612_);
v___x_2624_ = l_Lean_mkNatLit(v___x_2623_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2624_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2626_);
v___x_2628_ = v___x_2617_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_dec(v_a_2615_);
lean_dec(v_val_2612_);
v___x_2632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2632_);
v___x_2634_ = v___x_2617_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_val_2612_);
v_a_2637_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2614_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2614_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec(v_a_2608_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2645_);
v___x_2647_ = v___x_2610_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2607_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2607_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object* v_e_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Nat_reduceGcd___redArg(v_e_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec_ref(v_e_2658_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object* v_e_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Nat_reduceGcd___redArg(v_e_2665_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object* v_e_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Nat_reduceGcd(v_e_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_e_2675_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2702_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2703_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2700_, v___x_2701_, v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21____boxed(lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_();
return v_res_2705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2710_ = 1;
v___x_2711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_);
v___x_2712_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2709_, v___x_2710_, v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23____boxed(lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_();
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2717_ = 1;
v___x_2718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_);
v___x_2719_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2716_, v___x_2717_, v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25____boxed(lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_();
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg(lean_object* v_e_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_2734_ = lean_unsigned_to_nat(4u);
v___x_2735_ = l_Lean_Expr_isAppOfArity(v_e_2727_, v___x_2733_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec_ref(v_e_2727_);
v___x_2736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = l_Lean_Expr_appFn_x21(v_e_2727_);
v___x_2739_ = l_Lean_Expr_appArg_x21(v___x_2738_);
lean_dec_ref(v___x_2738_);
v___x_2740_ = l_Lean_Meta_getNatValue_x3f(v___x_2739_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
lean_dec_ref(v___x_2739_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2772_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2772_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2772_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
if (lean_obj_tag(v_a_2741_) == 1)
{
lean_object* v_val_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2743_);
v_val_2745_ = lean_ctor_get(v_a_2741_, 0);
lean_inc(v_val_2745_);
lean_dec_ref_known(v_a_2741_, 1);
v___x_2746_ = l_Lean_Expr_appArg_x21(v_e_2727_);
v___x_2747_ = l_Lean_Meta_getNatValue_x3f(v___x_2746_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
lean_dec_ref(v___x_2746_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2759_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
if (lean_obj_tag(v_a_2748_) == 1)
{
lean_object* v_val_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; 
lean_del_object(v___x_2750_);
v_val_2752_ = lean_ctor_get(v_a_2748_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v_a_2748_, 1);
v___x_2753_ = lean_nat_dec_lt(v_val_2745_, v_val_2752_);
lean_dec(v_val_2752_);
lean_dec(v_val_2745_);
v___x_2754_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2727_, v___x_2753_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
lean_dec(v_a_2748_);
lean_dec(v_val_2745_);
lean_dec_ref(v_e_2727_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2755_);
v___x_2757_ = v___x_2750_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_val_2745_);
lean_dec_ref(v_e_2727_);
v_a_2760_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2747_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2747_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
lean_dec(v_a_2741_);
lean_dec_ref(v_e_2727_);
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2768_);
v___x_2770_ = v___x_2743_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
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
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_e_2727_);
v_a_2773_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2740_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2740_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg___boxed(lean_object* v_e_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Nat_reduceLT___redArg(v_e_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object* v_e_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Nat_reduceLT___redArg(v_e_2788_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object* v_e_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Nat_reduceLT(v_e_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2828_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2829_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2826_, v___x_2827_, v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27____boxed(lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_();
return v_res_2831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2836_ = 1;
v___x_2837_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_);
v___x_2838_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2835_, v___x_2836_, v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29____boxed(lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_();
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2843_ = 1;
v___x_2844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_);
v___x_2845_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2842_, v___x_2843_, v___x_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31____boxed(lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_();
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg(lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = ((lean_object*)(l_Nat_reduceGT___redArg___closed__2));
v___x_2860_ = lean_unsigned_to_nat(4u);
v___x_2861_ = l_Lean_Expr_isAppOfArity(v_e_2853_, v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref(v_e_2853_);
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = l_Lean_Expr_appFn_x21(v_e_2853_);
v___x_2865_ = l_Lean_Expr_appArg_x21(v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = l_Lean_Meta_getNatValue_x3f(v___x_2865_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec_ref(v___x_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2898_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2898_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2898_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
if (lean_obj_tag(v_a_2867_) == 1)
{
lean_object* v_val_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_del_object(v___x_2869_);
v_val_2871_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_a_2867_, 1);
v___x_2872_ = l_Lean_Expr_appArg_x21(v_e_2853_);
v___x_2873_ = l_Lean_Meta_getNatValue_x3f(v___x_2872_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec_ref(v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2885_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2885_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2885_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
if (lean_obj_tag(v_a_2874_) == 1)
{
lean_object* v_val_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2876_);
v_val_2878_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v_a_2874_, 1);
v___x_2879_ = lean_nat_dec_lt(v_val_2878_, v_val_2871_);
lean_dec(v_val_2871_);
lean_dec(v_val_2878_);
v___x_2880_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2853_, v___x_2879_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_dec(v_a_2874_);
lean_dec(v_val_2871_);
lean_dec_ref(v_e_2853_);
v___x_2881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2881_);
v___x_2883_ = v___x_2876_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_val_2871_);
lean_dec_ref(v_e_2853_);
v_a_2886_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2873_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2873_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec(v_a_2867_);
lean_dec_ref(v_e_2853_);
v___x_2894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2894_);
v___x_2896_ = v___x_2869_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v_e_2853_);
v_a_2899_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2866_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2866_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg___boxed(lean_object* v_e_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Nat_reduceGT___redArg(v_e_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object* v_e_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Nat_reduceGT___redArg(v_e_2914_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object* v_e_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Nat_reduceGT(v_e_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_));
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2941_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2942_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2939_, v___x_2940_, v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27____boxed(lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_();
return v_res_2944_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2948_; uint8_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_));
v___x_2949_ = 1;
v___x_2950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_);
v___x_2951_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2948_, v___x_2949_, v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29____boxed(lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_();
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2955_; uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_));
v___x_2956_ = 1;
v___x_2957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_);
v___x_2958_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2955_, v___x_2956_, v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31____boxed(lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_();
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg(lean_object* v_e_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_2973_ = lean_unsigned_to_nat(4u);
v___x_2974_ = l_Lean_Expr_isAppOfArity(v_e_2966_, v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = l_Lean_Expr_appFn_x21(v_e_2966_);
v___x_2978_ = l_Lean_Expr_appArg_x21(v___x_2977_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = l_Lean_Meta_getNatValue_x3f(v___x_2978_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
lean_dec_ref(v___x_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3024_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_3024_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3024_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
if (lean_obj_tag(v_a_2980_) == 1)
{
lean_object* v_val_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3019_; 
v_val_2984_ = lean_ctor_get(v_a_2980_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_2986_ = v_a_2980_;
v_isShared_2987_ = v_isSharedCheck_3019_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_val_2984_);
lean_dec(v_a_2980_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3019_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_Expr_appArg_x21(v_e_2966_);
v___x_2989_ = l_Lean_Meta_getNatValue_x3f(v___x_2988_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
lean_dec_ref(v___x_2988_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3010_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3010_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3010_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___y_2995_; 
if (lean_obj_tag(v_a_2990_) == 1)
{
lean_object* v_val_3002_; uint8_t v___x_3003_; 
lean_del_object(v___x_2982_);
v_val_3002_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_val_3002_);
lean_dec_ref_known(v_a_2990_, 1);
v___x_3003_ = lean_nat_dec_eq(v_val_2984_, v_val_3002_);
lean_dec(v_val_3002_);
lean_dec(v_val_2984_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_2995_ = v___x_3004_;
goto v___jp_2994_;
}
else
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___y_2995_ = v___x_3005_;
goto v___jp_2994_;
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
lean_del_object(v___x_2992_);
lean_dec(v_a_2990_);
lean_del_object(v___x_2986_);
lean_dec(v_val_2984_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_3006_);
v___x_3008_ = v___x_2982_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
v___jp_2994_:
{
lean_object* v___x_2997_; 
lean_inc_ref(v___y_2995_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 0);
lean_ctor_set(v___x_2986_, 0, v___y_2995_);
v___x_2997_ = v___x_2986_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___y_2995_);
v___x_2997_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2997_);
v___x_2999_ = v___x_2992_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_del_object(v___x_2986_);
lean_dec(v_val_2984_);
lean_del_object(v___x_2982_);
v_a_3011_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2989_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2989_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
lean_dec(v_a_2980_);
v___x_3020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_3020_);
v___x_3022_ = v___x_2982_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
v_a_3025_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2979_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2979_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg___boxed(lean_object* v_e_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Nat_reduceBEq___redArg(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec_ref(v_e_3033_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object* v_e_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Nat_reduceBEq___redArg(v_e_3040_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object* v_e_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Nat_reduceBEq(v_e_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_e_3050_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_3080_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_3081_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3078_, v___x_3079_, v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27____boxed(lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_();
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_3088_ = 1;
v___x_3089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_);
v___x_3090_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3087_, v___x_3088_, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29____boxed(lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_();
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_3095_ = 1;
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_);
v___x_3097_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3094_, v___x_3095_, v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31____boxed(lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_();
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object* v_e_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3109_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_3110_ = lean_unsigned_to_nat(4u);
v___x_3111_ = l_Lean_Expr_isAppOfArity(v_e_3103_, v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = l_Lean_Expr_appFn_x21(v_e_3103_);
v___x_3115_ = l_Lean_Expr_appArg_x21(v___x_3114_);
lean_dec_ref(v___x_3114_);
v___x_3116_ = l_Lean_Meta_getNatValue_x3f(v___x_3115_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec_ref(v___x_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3161_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3161_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3161_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
if (lean_obj_tag(v_a_3117_) == 1)
{
lean_object* v_val_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3156_; 
v_val_3121_ = lean_ctor_get(v_a_3117_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_a_3117_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3123_ = v_a_3117_;
v_isShared_3124_ = v_isSharedCheck_3156_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_val_3121_);
lean_dec(v_a_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3156_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = l_Lean_Expr_appArg_x21(v_e_3103_);
v___x_3126_ = l_Lean_Meta_getNatValue_x3f(v___x_3125_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec_ref(v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3147_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3147_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3147_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___y_3132_; 
if (lean_obj_tag(v_a_3127_) == 1)
{
lean_object* v_val_3139_; uint8_t v___x_3140_; 
lean_del_object(v___x_3119_);
v_val_3139_ = lean_ctor_get(v_a_3127_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_a_3127_, 1);
v___x_3140_ = lean_nat_dec_eq(v_val_3121_, v_val_3139_);
lean_dec(v_val_3139_);
lean_dec(v_val_3121_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___y_3132_ = v___x_3141_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_3132_ = v___x_3142_;
goto v___jp_3131_;
}
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_del_object(v___x_3129_);
lean_dec(v_a_3127_);
lean_del_object(v___x_3123_);
lean_dec(v_val_3121_);
v___x_3143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3143_);
v___x_3145_ = v___x_3119_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
v___jp_3131_:
{
lean_object* v___x_3134_; 
lean_inc_ref(v___y_3132_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 0);
lean_ctor_set(v___x_3123_, 0, v___y_3132_);
v___x_3134_ = v___x_3123_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___y_3132_);
v___x_3134_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3134_);
v___x_3136_ = v___x_3129_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_del_object(v___x_3123_);
lean_dec(v_val_3121_);
lean_del_object(v___x_3119_);
v_a_3148_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3126_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3126_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_dec(v_a_3117_);
v___x_3157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3157_);
v___x_3159_ = v___x_3119_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3116_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3116_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object* v_e_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Nat_reduceBNe___redArg(v_e_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec_ref(v_e_3170_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object* v_e_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Nat_reduceBNe___redArg(v_e_3177_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object* v_e_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Nat_reduceBNe(v_e_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_e_3187_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_3216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_3217_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_3218_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3215_, v___x_3216_, v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27____boxed(lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_();
return v_res_3220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3224_; uint8_t v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_3225_ = 1;
v___x_3226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_);
v___x_3227_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3224_, v___x_3225_, v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29____boxed(lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_();
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_3232_ = 1;
v___x_3233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_);
v___x_3234_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3231_, v___x_3232_, v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31____boxed(lean_object* v_a_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_();
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg(lean_object* v_e_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v___x_3248_; 
lean_inc_ref(v_e_3242_);
v___x_3248_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3266_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3266_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3266_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = l_Lean_Expr_cleanupAnnotations(v_a_3249_);
v___x_3254_ = l_Lean_Expr_isApp(v___x_3253_);
if (v___x_3254_ == 0)
{
lean_dec_ref(v___x_3253_);
lean_del_object(v___x_3251_);
lean_dec_ref(v_e_3242_);
goto v___jp_3245_;
}
else
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3253_);
v___x_3256_ = l_Lean_Expr_isApp(v___x_3255_);
if (v___x_3256_ == 0)
{
lean_dec_ref(v___x_3255_);
lean_del_object(v___x_3251_);
lean_dec_ref(v_e_3242_);
goto v___jp_3245_;
}
else
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3255_);
v___x_3258_ = l_Lean_Expr_isApp(v___x_3257_);
if (v___x_3258_ == 0)
{
lean_dec_ref(v___x_3257_);
lean_del_object(v___x_3251_);
lean_dec_ref(v_e_3242_);
goto v___jp_3245_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3257_);
v___x_3260_ = ((lean_object*)(l_Nat_isValue___redArg___closed__2));
v___x_3261_ = l_Lean_Expr_isConstOf(v___x_3259_, v___x_3260_);
lean_dec_ref(v___x_3259_);
if (v___x_3261_ == 0)
{
lean_del_object(v___x_3251_);
lean_dec_ref(v_e_3242_);
goto v___jp_3245_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_e_3242_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3262_);
v___x_3264_ = v___x_3251_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec_ref(v_e_3242_);
v_a_3267_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3248_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3248_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
v___jp_3245_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg___boxed(lean_object* v_e_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Nat_isValue___redArg(v_e_3275_, v_a_3276_);
lean_dec(v_a_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object* v_e_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Nat_isValue___redArg(v_e_3279_, v_a_3284_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___boxed(lean_object* v_e_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Nat_isValue(v_e_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_));
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_));
v___x_3318_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3319_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3316_, v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23____boxed(lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_();
return v_res_3321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_));
v___x_3326_ = 1;
v___x_3327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_);
v___x_3328_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3325_, v___x_3326_, v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25____boxed(lean_object* v_a_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_();
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___impl(lean_object* v_x_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_obj_tag_nat(v_x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___impl___boxed(lean_object* v_x_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___impl(v_x_3333_);
lean_dec_ref(v_x_3333_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(lean_object* v_t_3335_, lean_object* v_k_3336_){
_start:
{
if (lean_obj_tag(v_t_3335_) == 0)
{
lean_object* v_n_3337_; lean_object* v___x_3338_; 
v_n_3337_ = lean_ctor_get(v_t_3335_, 0);
lean_inc(v_n_3337_);
lean_dec_ref_known(v_t_3335_, 1);
v___x_3338_ = lean_apply_1(v_k_3336_, v_n_3337_);
return v___x_3338_;
}
else
{
lean_object* v_e_3339_; lean_object* v_o_3340_; lean_object* v_n_3341_; lean_object* v___x_3342_; 
v_e_3339_ = lean_ctor_get(v_t_3335_, 0);
lean_inc_ref(v_e_3339_);
v_o_3340_ = lean_ctor_get(v_t_3335_, 1);
lean_inc_ref(v_o_3340_);
v_n_3341_ = lean_ctor_get(v_t_3335_, 2);
lean_inc(v_n_3341_);
lean_dec_ref_known(v_t_3335_, 3);
v___x_3342_ = lean_apply_3(v_k_3336_, v_e_3339_, v_o_3340_, v_n_3341_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(lean_object* v_motive_3343_, lean_object* v_ctorIdx_3344_, lean_object* v_t_3345_, lean_object* v_h_3346_, lean_object* v_k_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3345_, v_k_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___boxed(lean_object* v_motive_3349_, lean_object* v_ctorIdx_3350_, lean_object* v_t_3351_, lean_object* v_h_3352_, lean_object* v_k_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(v_motive_3349_, v_ctorIdx_3350_, v_t_3351_, v_h_3352_, v_k_3353_);
lean_dec(v_ctorIdx_3350_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim___redArg(lean_object* v_t_3355_, lean_object* v_const_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3355_, v_const_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim(lean_object* v_motive_3358_, lean_object* v_t_3359_, lean_object* v_h_3360_, lean_object* v_const_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3359_, v_const_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim___redArg(lean_object* v_t_3363_, lean_object* v_offset_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3363_, v_offset_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim(lean_object* v_motive_3366_, lean_object* v_t_3367_, lean_object* v_h_3368_, lean_object* v_offset_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3367_, v_offset_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(lean_object* v_e_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3385_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_3386_ = lean_unsigned_to_nat(6u);
v___x_3387_ = l_Lean_Expr_isAppOfArity(v_e_3379_, v___x_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2));
v___x_3389_ = lean_unsigned_to_nat(4u);
v___x_3390_ = l_Lean_Expr_isAppOfArity(v_e_3379_, v___x_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3));
v___x_3392_ = lean_unsigned_to_nat(2u);
v___x_3393_ = l_Lean_Expr_isAppOfArity(v_e_3379_, v___x_3391_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3394_ = ((lean_object*)(l_Nat_reduceSucc___redArg___closed__2));
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = l_Lean_Expr_isAppOfArity(v_e_3379_, v___x_3394_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = lean_box(0);
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
return v___x_3398_;
}
else
{
lean_object* v_b_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_b_3399_ = l_Lean_Expr_appArg_x21(v_e_3379_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_b_3399_);
lean_ctor_set(v___x_3400_, 1, v___x_3395_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
else
{
lean_object* v___x_3403_; lean_object* v_b_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3403_ = l_Lean_Expr_appFn_x21(v_e_3379_);
v_b_3404_ = l_Lean_Expr_appArg_x21(v___x_3403_);
lean_dec_ref(v___x_3403_);
v___x_3405_ = l_Lean_Expr_appArg_x21(v_e_3379_);
v___x_3406_ = l_Lean_Meta_getNatValue_x3f(v___x_3405_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec_ref(v___x_3405_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3427_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3427_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3427_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
if (lean_obj_tag(v_a_3407_) == 1)
{
lean_object* v_val_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3422_; 
v_val_3411_ = lean_ctor_get(v_a_3407_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3413_ = v_a_3407_;
v_isShared_3414_ = v_isSharedCheck_3422_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_val_3411_);
lean_dec(v_a_3407_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3422_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_b_3404_);
lean_ctor_set(v___x_3415_, 1, v_val_3411_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3417_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
lean_dec(v_a_3407_);
lean_dec_ref(v_b_3404_);
v___x_3423_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3423_);
v___x_3425_ = v___x_3409_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref(v_b_3404_);
v_a_3428_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3406_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3406_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v_inst_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3436_ = l_Lean_Expr_appFn_x21(v_e_3379_);
v___x_3437_ = l_Lean_Expr_appFn_x21(v___x_3436_);
v_inst_3438_ = l_Lean_Expr_appArg_x21(v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = l_Lean_Nat_mkInstAdd;
v___x_3440_ = l_Lean_Meta_matchesInstance(v_inst_3438_, v___x_3439_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3482_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3482_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3482_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_unbox(v_a_3441_);
lean_dec(v_a_3441_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_dec_ref(v___x_3436_);
v___x_3446_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3446_);
v___x_3448_ = v___x_3443_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_del_object(v___x_3443_);
v___x_3450_ = l_Lean_Expr_appArg_x21(v___x_3436_);
lean_dec_ref(v___x_3436_);
v___x_3451_ = l_Lean_Expr_appArg_x21(v_e_3379_);
v___x_3452_ = l_Lean_Meta_getNatValue_x3f(v___x_3451_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec_ref(v___x_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3473_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3473_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3473_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
if (lean_obj_tag(v_a_3453_) == 1)
{
lean_object* v_val_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3468_; 
v_val_3457_ = lean_ctor_get(v_a_3453_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3453_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3459_ = v_a_3453_;
v_isShared_3460_ = v_isSharedCheck_3468_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_val_3457_);
lean_dec(v_a_3453_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3468_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3450_);
lean_ctor_set(v___x_3461_, 1, v_val_3457_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3461_);
v___x_3463_ = v___x_3459_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3463_);
v___x_3465_ = v___x_3455_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
lean_dec(v_a_3453_);
lean_dec_ref(v___x_3450_);
v___x_3469_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3469_);
v___x_3471_ = v___x_3455_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v___x_3450_);
v_a_3474_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3452_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3452_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___x_3436_);
v_a_3483_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3440_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3440_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v_inst_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3491_ = l_Lean_Expr_appFn_x21(v_e_3379_);
v___x_3492_ = l_Lean_Expr_appFn_x21(v___x_3491_);
v_inst_3493_ = l_Lean_Expr_appArg_x21(v___x_3492_);
lean_dec_ref(v___x_3492_);
v___x_3494_ = l_Lean_Nat_mkInstHAdd;
v___x_3495_ = l_Lean_Meta_matchesInstance(v_inst_3493_, v___x_3494_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3537_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3537_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3537_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
uint8_t v___x_3500_; 
v___x_3500_ = lean_unbox(v_a_3496_);
lean_dec(v_a_3496_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
lean_dec_ref(v___x_3491_);
v___x_3501_ = lean_box(0);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3501_);
v___x_3503_ = v___x_3498_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_del_object(v___x_3498_);
v___x_3505_ = l_Lean_Expr_appArg_x21(v___x_3491_);
lean_dec_ref(v___x_3491_);
v___x_3506_ = l_Lean_Expr_appArg_x21(v_e_3379_);
v___x_3507_ = l_Lean_Meta_getNatValue_x3f(v___x_3506_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec_ref(v___x_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3528_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3528_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3528_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
if (lean_obj_tag(v_a_3508_) == 1)
{
lean_object* v_val_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3523_; 
v_val_3512_ = lean_ctor_get(v_a_3508_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_a_3508_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3514_ = v_a_3508_;
v_isShared_3515_ = v_isSharedCheck_3523_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_val_3512_);
lean_dec(v_a_3508_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3523_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3505_);
lean_ctor_set(v___x_3516_, 1, v_val_3512_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3516_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3518_);
v___x_3520_ = v___x_3510_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
lean_dec(v_a_3508_);
lean_dec_ref(v___x_3505_);
v___x_3524_ = lean_box(0);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3524_);
v___x_3526_ = v___x_3510_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v___x_3505_);
v_a_3529_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3507_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3507_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec_ref(v___x_3491_);
v_a_3538_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3495_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3495_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___boxed(lean_object* v_e_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec_ref(v_e_3546_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object* v_e_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3553_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object* v_e_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(v_e_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_e_3563_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(lean_object* v_e_3573_, lean_object* v_inc_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_e_3580_; lean_object* v___x_3581_; 
v_e_3580_ = l_Lean_Expr_consumeMData(v_e_3573_);
lean_dec_ref(v_e_3573_);
v___x_3581_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3580_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
if (lean_obj_tag(v_a_3582_) == 0)
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_nat_dec_eq(v_inc_3574_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3593_; 
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v___x_3581_, 0);
lean_dec(v_unused_3594_);
v___x_3586_ = v___x_3581_;
v_isShared_3587_ = v_isSharedCheck_3593_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v___x_3581_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3593_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v_e_3580_);
lean_ctor_set(v___x_3588_, 1, v_inc_3574_);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3589_);
v___x_3591_ = v___x_3586_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
else
{
lean_dec_ref(v_e_3580_);
lean_dec(v_inc_3574_);
return v___x_3581_;
}
}
else
{
lean_object* v_val_3595_; lean_object* v_fst_3596_; lean_object* v_snd_3597_; lean_object* v___x_3598_; 
lean_inc_ref(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
lean_dec_ref(v_e_3580_);
v_val_3595_ = lean_ctor_get(v_a_3582_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v_a_3582_, 1);
v_fst_3596_ = lean_ctor_get(v_val_3595_, 0);
lean_inc(v_fst_3596_);
v_snd_3597_ = lean_ctor_get(v_val_3595_, 1);
lean_inc(v_snd_3597_);
lean_dec(v_val_3595_);
v___x_3598_ = lean_nat_add(v_inc_3574_, v_snd_3597_);
lean_dec(v_snd_3597_);
lean_dec(v_inc_3574_);
v_e_3573_ = v_fst_3596_;
v_inc_3574_ = v___x_3598_;
goto _start;
}
}
else
{
lean_dec_ref(v_e_3580_);
lean_dec(v_inc_3574_);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg___boxed(lean_object* v_e_3600_, lean_object* v_inc_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3600_, v_inc_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object* v_e_3608_, lean_object* v_inc_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3608_, v_inc_3609_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object* v_e_3619_, lean_object* v_inc_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(v_e_3619_, v_inc_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(lean_object* v_e_3630_, lean_object* v_inc_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Meta_getNatValue_x3f(v_e_3630_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3688_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3688_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3688_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
if (lean_obj_tag(v_a_3638_) == 0)
{
lean_object* v___x_3642_; 
lean_del_object(v___x_3640_);
v___x_3642_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3630_, v_inc_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3666_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
if (lean_obj_tag(v_a_3643_) == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3647_ = lean_box(0);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3647_);
v___x_3649_ = v___x_3645_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
else
{
lean_object* v_val_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3665_; 
v_val_3651_ = lean_ctor_get(v_a_3643_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3653_ = v_a_3643_;
v_isShared_3654_ = v_isSharedCheck_3665_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_val_3651_);
lean_dec(v_a_3643_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3665_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_fst_3655_; lean_object* v_snd_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v_fst_3655_ = lean_ctor_get(v_val_3651_, 0);
lean_inc(v_fst_3655_);
v_snd_3656_ = lean_ctor_get(v_val_3651_, 1);
lean_inc_n(v_snd_3656_, 2);
lean_dec(v_val_3651_);
v___x_3657_ = l_Lean_mkNatLit(v_snd_3656_);
v___x_3658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3658_, 0, v_fst_3655_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
lean_ctor_set(v___x_3658_, 2, v_snd_3656_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3658_);
v___x_3660_ = v___x_3653_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3662_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3660_);
v___x_3662_ = v___x_3645_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_a_3667_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3642_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3642_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_val_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v_e_3630_);
v_val_3675_ = lean_ctor_get(v_a_3638_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_a_3638_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3677_ = v_a_3638_;
v_isShared_3678_ = v_isSharedCheck_3687_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_val_3675_);
lean_dec(v_a_3638_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3687_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3679_ = lean_nat_add(v_val_3675_, v_inc_3631_);
lean_dec(v_inc_3631_);
lean_dec(v_val_3675_);
v___x_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v___x_3680_);
v___x_3682_ = v___x_3677_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3684_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3682_);
v___x_3684_ = v___x_3640_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_inc_3631_);
lean_dec_ref(v_e_3630_);
v_a_3689_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3637_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3637_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg___boxed(lean_object* v_e_3697_, lean_object* v_inc_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_e_3697_, v_inc_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
lean_dec(v_a_3702_);
lean_dec_ref(v_a_3701_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object* v_e_3705_, lean_object* v_inc_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_e_3705_, v_inc_3706_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object* v_e_3716_, lean_object* v_inc_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(v_e_3716_, v_inc_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
return v_res_3726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v_nat_3729_; 
v___x_3727_ = lean_box(0);
v___x_3728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v_nat_3729_ = l_Lean_mkConst(v___x_3728_, v___x_3727_);
return v_nat_3729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2));
v___x_3738_ = l_Lean_mkConst(v___x_3737_, v___x_3736_);
return v___x_3738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = lean_box(0);
v___x_3743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6));
v___x_3744_ = l_Lean_mkConst(v___x_3743_, v___x_3742_);
return v___x_3744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8(void){
_start:
{
lean_object* v___x_3745_; lean_object* v_nat_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7);
v_nat_3746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3747_ = lean_unsigned_to_nat(2u);
v___x_3748_ = lean_mk_empty_array_with_capacity(v___x_3747_);
v___x_3749_ = lean_array_push(v___x_3748_, v_nat_3746_);
v___x_3750_ = lean_array_push(v___x_3749_, v___x_3745_);
return v___x_3750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v_instHAdd_3753_; 
v___x_3751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8);
v___x_3752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4);
v_instHAdd_3753_ = l_Lean_mkAppN(v___x_3752_, v___x_3751_);
return v_instHAdd_3753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11));
v___x_3761_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_3762_ = l_Lean_mkConst(v___x_3761_, v___x_3760_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13(void){
_start:
{
lean_object* v_nat_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_nat_3763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3764_ = lean_unsigned_to_nat(6u);
v___x_3765_ = lean_mk_empty_array_with_capacity(v___x_3764_);
v___x_3766_ = lean_array_push(v___x_3765_, v_nat_3763_);
return v___x_3766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14(void){
_start:
{
lean_object* v_nat_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_nat_3767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13);
v___x_3769_ = lean_array_push(v___x_3768_, v_nat_3767_);
return v___x_3769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15(void){
_start:
{
lean_object* v_nat_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_nat_3770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14);
v___x_3772_ = lean_array_push(v___x_3771_, v_nat_3770_);
return v___x_3772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16(void){
_start:
{
lean_object* v_instHAdd_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_instHAdd_3773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9);
v___x_3774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
v___x_3775_ = lean_array_push(v___x_3774_, v_instHAdd_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object* v_x_3776_, lean_object* v_y_3777_){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3778_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12);
v___x_3779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16);
v___x_3780_ = lean_array_push(v___x_3779_, v_x_3776_);
v___x_3781_ = lean_array_push(v___x_3780_, v_y_3777_);
v___x_3782_ = l_Lean_mkAppN(v___x_3778_, v___x_3781_);
lean_dec_ref(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v_instSub_3788_; 
v___x_3786_ = lean_box(0);
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1));
v_instSub_3788_ = l_Lean_mkConst(v___x_3787_, v___x_3786_);
return v_instSub_3788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4));
v___x_3794_ = l_Lean_mkConst(v___x_3793_, v___x_3792_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6(void){
_start:
{
lean_object* v_instSub_3795_; lean_object* v_nat_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_instSub_3795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2);
v_nat_3796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3797_ = lean_unsigned_to_nat(2u);
v___x_3798_ = lean_mk_empty_array_with_capacity(v___x_3797_);
v___x_3799_ = lean_array_push(v___x_3798_, v_nat_3796_);
v___x_3800_ = lean_array_push(v___x_3799_, v_instSub_3795_);
return v___x_3800_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v_instHSub_3803_; 
v___x_3801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6);
v___x_3802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5);
v_instHSub_3803_ = l_Lean_mkAppN(v___x_3802_, v___x_3801_);
return v_instHSub_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11));
v___x_3805_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_3806_ = l_Lean_mkConst(v___x_3805_, v___x_3804_);
return v___x_3806_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9(void){
_start:
{
lean_object* v_instHSub_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_instHSub_3807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7);
v___x_3808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
v___x_3809_ = lean_array_push(v___x_3808_, v_instHSub_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object* v_x_3810_, lean_object* v_y_3811_){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8);
v___x_3813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9);
v___x_3814_ = lean_array_push(v___x_3813_, v_x_3810_);
v___x_3815_ = lean_array_push(v___x_3814_, v_y_3811_);
v___x_3816_ = l_Lean_mkAppN(v___x_3812_, v___x_3815_);
lean_dec_ref(v___x_3815_);
return v___x_3816_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_box(0);
v___x_3821_ = l_Lean_Level_succ___override(v___x_3820_);
return v___x_3821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = lean_box(0);
v___x_3823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2);
v___x_3824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v___x_3822_);
return v___x_3824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3);
v___x_3826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_3827_ = l_Lean_mkConst(v___x_3826_, v___x_3825_);
return v___x_3827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3829_ = lean_unsigned_to_nat(3u);
v___x_3830_ = lean_mk_empty_array_with_capacity(v___x_3829_);
v___x_3831_ = lean_array_push(v___x_3830_, v___x_3828_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object* v_x_3832_, lean_object* v_y_3833_){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4);
v___x_3835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5);
v___x_3836_ = lean_array_push(v___x_3835_, v_x_3832_);
v___x_3837_ = lean_array_push(v___x_3836_, v_y_3833_);
v___x_3838_ = l_Lean_mkAppN(v___x_3834_, v___x_3837_);
lean_dec_ref(v___x_3837_);
return v___x_3838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1));
v___x_3844_ = l_Lean_mkConst(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = lean_box(0);
v___x_3849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4));
v___x_3850_ = l_Lean_mkConst(v___x_3849_, v___x_3848_);
return v___x_3850_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3851_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5);
v___x_3852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3853_ = lean_unsigned_to_nat(2u);
v___x_3854_ = lean_mk_empty_array_with_capacity(v___x_3853_);
v___x_3855_ = lean_array_push(v___x_3854_, v___x_3852_);
v___x_3856_ = lean_array_push(v___x_3855_, v___x_3851_);
return v___x_3856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6);
v___x_3858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2);
v___x_3859_ = l_Lean_mkAppN(v___x_3858_, v___x_3857_);
return v___x_3859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance(void){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7);
return v___x_3860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3862_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_3863_ = l_Lean_mkConst(v___x_3862_, v___x_3861_);
return v___x_3863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3865_ = lean_unsigned_to_nat(4u);
v___x_3866_ = lean_mk_empty_array_with_capacity(v___x_3865_);
v___x_3867_ = lean_array_push(v___x_3866_, v___x_3864_);
return v___x_3867_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3868_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
v___x_3869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3870_ = lean_array_push(v___x_3869_, v___x_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object* v_x_3871_, lean_object* v_y_3872_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0);
v___x_3874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2);
v___x_3875_ = lean_array_push(v___x_3874_, v_x_3871_);
v___x_3876_ = lean_array_push(v___x_3875_, v_y_3872_);
v___x_3877_ = l_Lean_mkAppN(v___x_3873_, v___x_3876_);
lean_dec_ref(v___x_3876_);
return v___x_3877_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3879_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_3880_ = l_Lean_mkConst(v___x_3879_, v___x_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object* v_x_3881_, lean_object* v_y_3882_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0);
v___x_3884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2);
v___x_3885_ = lean_array_push(v___x_3884_, v_x_3881_);
v___x_3886_ = lean_array_push(v___x_3885_, v_y_3882_);
v___x_3887_ = l_Lean_mkAppN(v___x_3883_, v___x_3886_);
lean_dec_ref(v___x_3886_);
return v___x_3887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_3895_ = l_Lean_Expr_const___override(v___x_3894_, v___x_3893_);
return v___x_3895_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = lean_box(0);
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5));
v___x_3901_ = l_Lean_mkConst(v___x_3900_, v___x_3899_);
return v___x_3901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6);
v___x_3903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3904_ = lean_array_push(v___x_3903_, v___x_3902_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object* v_x_3905_, lean_object* v_y_3906_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3);
v___x_3908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7);
v___x_3909_ = lean_array_push(v___x_3908_, v_x_3905_);
v___x_3910_ = lean_array_push(v___x_3909_, v_y_3906_);
v___x_3911_ = l_Lean_mkAppN(v___x_3907_, v___x_3910_);
lean_dec_ref(v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object* v_x_3912_, lean_object* v_y_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_y_3913_, v_x_3912_);
return v___x_3914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3916_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_3917_ = l_Lean_Expr_const___override(v___x_3916_, v___x_3915_);
return v___x_3917_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_box(0);
v___x_3922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2));
v___x_3923_ = l_Lean_mkConst(v___x_3922_, v___x_3921_);
return v___x_3923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3);
v___x_3925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3926_ = lean_array_push(v___x_3925_, v___x_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object* v_x_3927_, lean_object* v_y_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0);
v___x_3930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4);
v___x_3931_ = lean_array_push(v___x_3930_, v_x_3927_);
v___x_3932_ = lean_array_push(v___x_3931_, v_y_3928_);
v___x_3933_ = l_Lean_mkAppN(v___x_3929_, v___x_3932_);
lean_dec_ref(v___x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object* v_x_3934_, lean_object* v_y_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_3935_, v_x_3934_);
return v___x_3936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = lean_box(0);
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1));
v___x_3942_ = l_Lean_mkConst(v___x_3941_, v___x_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object* v_p_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___x_3949_; 
lean_inc_ref(v_p_3943_);
v___x_3949_ = l_Lean_Meta_mkDecide(v_p_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
v___x_3951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___x_3952_ = l_Lean_Meta_mkEqRefl(v___x_3951_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3968_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3968_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3968_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2);
v___x_3958_ = l_Lean_Expr_appArg_x21(v_a_3950_);
lean_dec(v_a_3950_);
v___x_3959_ = lean_unsigned_to_nat(3u);
v___x_3960_ = lean_mk_empty_array_with_capacity(v___x_3959_);
v___x_3961_ = lean_array_push(v___x_3960_, v_p_3943_);
v___x_3962_ = lean_array_push(v___x_3961_, v___x_3958_);
v___x_3963_ = lean_array_push(v___x_3962_, v_a_3953_);
v___x_3964_ = l_Lean_mkAppN(v___x_3957_, v___x_3963_);
lean_dec_ref(v___x_3963_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_3964_);
v___x_3966_ = v___x_3955_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
else
{
lean_dec(v_a_3950_);
lean_dec_ref(v_p_3943_);
return v___x_3952_;
}
}
else
{
lean_dec_ref(v_p_3943_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___boxed(lean_object* v_p_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v_p_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(lean_object* v_expr_3976_, lean_object* v_nm_3977_, lean_object* v_args_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___x_3981_; lean_object* v_env_3982_; uint8_t v___x_3983_; uint8_t v___x_3984_; 
v___x_3981_ = lean_st_ref_get(v_a_3979_);
v_env_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc_ref(v_env_3982_);
lean_dec(v___x_3981_);
v___x_3983_ = 1;
lean_inc(v_nm_3977_);
v___x_3984_ = l_Lean_Environment_contains(v_env_3982_, v_nm_3977_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_dec(v_nm_3977_);
lean_dec_ref(v_expr_3976_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3987_ = lean_box(0);
v___x_3988_ = l_Lean_mkConst(v_nm_3977_, v___x_3987_);
v___x_3989_ = l_Lean_mkAppN(v___x_3988_, v_args_3978_);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3991_, 0, v_expr_3976_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
lean_ctor_set_uint8(v___x_3991_, sizeof(void*)*2, v___x_3983_);
v___x_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg___boxed(lean_object* v_expr_3994_, lean_object* v_nm_3995_, lean_object* v_args_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v_expr_3994_, v_nm_3995_, v_args_3996_, v_a_3997_);
lean_dec(v_a_3997_);
lean_dec_ref(v_args_3996_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst(lean_object* v_expr_4000_, lean_object* v_nm_4001_, lean_object* v_args_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v_expr_4000_, v_nm_4001_, v_args_4002_, v_a_4009_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___boxed(lean_object* v_expr_4012_, lean_object* v_nm_4013_, lean_object* v_args_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst(v_expr_4012_, v_nm_4013_, v_args_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_args_4014_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___impl(lean_object* v_x_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_obj_tag_nat(v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___impl___boxed(lean_object* v_x_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___impl(v_x_4026_);
lean_dec_ref(v_x_4026_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(lean_object* v_t_4028_, lean_object* v_k_4029_){
_start:
{
switch(lean_obj_tag(v_t_4028_))
{
case 0:
{
uint8_t v_b_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_b_4030_ = lean_ctor_get_uint8(v_t_4028_, 0);
lean_dec_ref_known(v_t_4028_, 0);
v___x_4031_ = lean_box(v_b_4030_);
v___x_4032_ = lean_apply_1(v_k_4029_, v___x_4031_);
return v___x_4032_;
}
case 1:
{
lean_object* v_p_4033_; lean_object* v___x_4034_; 
v_p_4033_ = lean_ctor_get(v_t_4028_, 0);
lean_inc_ref(v_p_4033_);
lean_dec_ref_known(v_t_4028_, 1);
v___x_4034_ = lean_apply_1(v_k_4029_, v_p_4033_);
return v___x_4034_;
}
default: 
{
lean_object* v_x_4035_; lean_object* v_y_4036_; lean_object* v_p_4037_; lean_object* v___x_4038_; 
v_x_4035_ = lean_ctor_get(v_t_4028_, 0);
lean_inc_ref(v_x_4035_);
v_y_4036_ = lean_ctor_get(v_t_4028_, 1);
lean_inc_ref(v_y_4036_);
v_p_4037_ = lean_ctor_get(v_t_4028_, 2);
lean_inc_ref(v_p_4037_);
lean_dec_ref_known(v_t_4028_, 3);
v___x_4038_ = lean_apply_3(v_k_4029_, v_x_4035_, v_y_4036_, v_p_4037_);
return v___x_4038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim(lean_object* v_motive_4039_, lean_object* v_ctorIdx_4040_, lean_object* v_t_4041_, lean_object* v_h_4042_, lean_object* v_k_4043_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4041_, v_k_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___boxed(lean_object* v_motive_4045_, lean_object* v_ctorIdx_4046_, lean_object* v_t_4047_, lean_object* v_h_4048_, lean_object* v_k_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim(v_motive_4045_, v_ctorIdx_4046_, v_t_4047_, v_h_4048_, v_k_4049_);
lean_dec(v_ctorIdx_4046_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_decide_elim___redArg(lean_object* v_t_4051_, lean_object* v_decide_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4051_, v_decide_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_decide_elim(lean_object* v_motive_4054_, lean_object* v_t_4055_, lean_object* v_h_4056_, lean_object* v_decide_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4055_, v_decide_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_false_elim___redArg(lean_object* v_t_4059_, lean_object* v_false_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4059_, v_false_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_false_elim(lean_object* v_motive_4062_, lean_object* v_t_4063_, lean_object* v_h_4064_, lean_object* v_false_4065_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4063_, v_false_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_eq_elim___redArg(lean_object* v_t_4067_, lean_object* v_eq_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4067_, v_eq_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_eq_elim(lean_object* v_motive_4070_, lean_object* v_t_4071_, lean_object* v_h_4072_, lean_object* v_eq_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_4071_, v_eq_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(lean_object* v_e_4075_, lean_object* v_lemmaName_4076_, lean_object* v_args_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v___x_4080_; lean_object* v_env_4081_; uint8_t v___x_4082_; uint8_t v___x_4083_; 
v___x_4080_ = lean_st_ref_get(v_a_4078_);
v_env_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4081_);
lean_dec(v___x_4080_);
v___x_4082_ = 1;
lean_inc(v_lemmaName_4076_);
v___x_4083_ = l_Lean_Environment_contains(v_env_4081_, v_lemmaName_4076_, v___x_4082_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec(v_lemmaName_4076_);
lean_dec_ref(v_e_4075_);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
else
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4086_ = lean_box(0);
v___x_4087_ = l_Lean_mkConst(v_lemmaName_4076_, v___x_4086_);
v___x_4088_ = l_Lean_mkAppN(v___x_4087_, v_args_4077_);
v___x_4089_ = lean_apply_1(v_e_4075_, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
return v___x_4091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg___boxed(lean_object* v_e_4092_, lean_object* v_lemmaName_4093_, lean_object* v_args_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v_e_4092_, v_lemmaName_4093_, v_args_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec_ref(v_args_4094_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma(lean_object* v_e_4098_, lean_object* v_lemmaName_4099_, lean_object* v_args_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v_e_4098_, v_lemmaName_4099_, v_args_4100_, v_a_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___boxed(lean_object* v_e_4110_, lean_object* v_lemmaName_4111_, lean_object* v_args_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma(v_e_4110_, v_lemmaName_4111_, v_args_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
lean_dec(v_a_4115_);
lean_dec_ref(v_a_4114_);
lean_dec(v_a_4113_);
lean_dec_ref(v_args_4112_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__0(lean_object* v_p_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_p_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2(lean_object* v_n_4124_, lean_object* v_n_4125_, lean_object* v_e_4126_, lean_object* v_p_4127_){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4128_ = lean_nat_sub(v_n_4124_, v_n_4125_);
v___x_4129_ = l_Lean_mkNatLit(v___x_4128_);
v___x_4130_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4130_, 0, v_e_4126_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
lean_ctor_set(v___x_4130_, 2, v_p_4127_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed(lean_object* v_n_4131_, lean_object* v_n_4132_, lean_object* v_e_4133_, lean_object* v_p_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2(v_n_4131_, v_n_4132_, v_e_4133_, v_p_4134_);
lean_dec(v_n_4132_);
lean_dec(v_n_4131_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__3(lean_object* v___x_4136_, lean_object* v_e_4137_, lean_object* v_p_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4136_);
lean_ctor_set(v___x_4139_, 1, v_e_4137_);
lean_ctor_set(v___x_4139_, 2, v_p_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__1(lean_object* v_e_4140_, lean_object* v___y_4141_, lean_object* v_p_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4143_, 0, v_e_4140_);
lean_ctor_set(v___x_4143_, 1, v___y_4141_);
lean_ctor_set(v___x_4143_, 2, v_p_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(lean_object* v_x_4176_, lean_object* v_y_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v___f_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___f_4183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0));
v___x_4184_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_x_4176_);
v___x_4185_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_4176_, v___x_4184_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4375_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4375_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4375_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
if (lean_obj_tag(v_a_4186_) == 1)
{
lean_object* v_val_4190_; lean_object* v___x_4191_; 
lean_del_object(v___x_4188_);
v_val_4190_ = lean_ctor_get(v_a_4186_, 0);
lean_inc(v_val_4190_);
lean_dec_ref_known(v_a_4186_, 1);
lean_inc_ref(v_y_4177_);
v___x_4191_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_4177_, v___x_4184_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4362_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4362_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4362_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
if (lean_obj_tag(v_a_4192_) == 1)
{
if (lean_obj_tag(v_val_4190_) == 0)
{
lean_object* v_val_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref(v_y_4177_);
v_val_4196_ = lean_ctor_get(v_a_4192_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_a_4192_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4198_ = v_a_4192_;
v_isShared_4199_ = v_isSharedCheck_4254_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_val_4196_);
lean_dec(v_a_4192_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4254_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
if (lean_obj_tag(v_val_4196_) == 0)
{
lean_object* v_n_4200_; lean_object* v_n_4201_; uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4205_; 
lean_dec_ref(v_x_4176_);
v_n_4200_ = lean_ctor_get(v_val_4190_, 0);
lean_inc(v_n_4200_);
lean_dec_ref_known(v_val_4190_, 1);
v_n_4201_ = lean_ctor_get(v_val_4196_, 0);
lean_inc(v_n_4201_);
lean_dec_ref_known(v_val_4196_, 1);
v___x_4202_ = lean_nat_dec_eq(v_n_4200_, v_n_4201_);
lean_dec(v_n_4201_);
lean_dec(v_n_4200_);
v___x_4203_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_4203_, 0, v___x_4202_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4203_);
v___x_4205_ = v___x_4198_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
lean_object* v___x_4207_; 
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4205_);
v___x_4207_ = v___x_4194_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
else
{
lean_object* v_n_4210_; lean_object* v_e_4211_; lean_object* v_o_4212_; lean_object* v_n_4213_; uint8_t v___x_4214_; 
lean_del_object(v___x_4198_);
lean_del_object(v___x_4194_);
v_n_4210_ = lean_ctor_get(v_val_4190_, 0);
lean_inc(v_n_4210_);
lean_dec_ref_known(v_val_4190_, 1);
v_e_4211_ = lean_ctor_get(v_val_4196_, 0);
lean_inc_ref(v_e_4211_);
v_o_4212_ = lean_ctor_get(v_val_4196_, 1);
lean_inc_ref(v_o_4212_);
v_n_4213_ = lean_ctor_get(v_val_4196_, 2);
lean_inc(v_n_4213_);
lean_dec_ref_known(v_val_4196_, 3);
v___x_4214_ = lean_nat_dec_le(v_n_4213_, v_n_4210_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
lean_dec(v_n_4213_);
lean_dec(v_n_4210_);
lean_inc_ref(v_o_4212_);
lean_inc_ref(v_x_4176_);
v___x_4215_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_x_4176_, v_o_4212_);
v___x_4216_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4215_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v___x_4218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3));
v___x_4219_ = lean_unsigned_to_nat(4u);
v___x_4220_ = lean_mk_empty_array_with_capacity(v___x_4219_);
v___x_4221_ = lean_array_push(v___x_4220_, v_x_4176_);
v___x_4222_ = lean_array_push(v___x_4221_, v_e_4211_);
v___x_4223_ = lean_array_push(v___x_4222_, v_o_4212_);
v___x_4224_ = lean_array_push(v___x_4223_, v_a_4217_);
v___x_4225_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4183_, v___x_4218_, v___x_4224_, v_a_4181_);
lean_dec_ref(v___x_4224_);
return v___x_4225_;
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v_o_4212_);
lean_dec_ref(v_e_4211_);
lean_dec_ref(v_x_4176_);
v_a_4226_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4216_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4216_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
else
{
lean_object* v___f_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_inc_ref(v_e_4211_);
v___f_4234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4234_, 0, v_n_4210_);
lean_closure_set(v___f_4234_, 1, v_n_4213_);
lean_closure_set(v___f_4234_, 2, v_e_4211_);
lean_inc_ref(v_x_4176_);
lean_inc_ref(v_o_4212_);
v___x_4235_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4212_, v_x_4176_);
v___x_4236_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4235_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5));
v___x_4239_ = lean_unsigned_to_nat(4u);
v___x_4240_ = lean_mk_empty_array_with_capacity(v___x_4239_);
v___x_4241_ = lean_array_push(v___x_4240_, v_x_4176_);
v___x_4242_ = lean_array_push(v___x_4241_, v_e_4211_);
v___x_4243_ = lean_array_push(v___x_4242_, v_o_4212_);
v___x_4244_ = lean_array_push(v___x_4243_, v_a_4237_);
v___x_4245_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4234_, v___x_4238_, v___x_4244_, v_a_4181_);
lean_dec_ref(v___x_4244_);
return v___x_4245_;
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v___f_4234_);
lean_dec_ref(v_o_4212_);
lean_dec_ref(v_e_4211_);
lean_dec_ref(v_x_4176_);
v_a_4246_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4236_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4236_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_4255_; 
lean_del_object(v___x_4194_);
lean_dec_ref(v_x_4176_);
v_val_4255_ = lean_ctor_get(v_a_4192_, 0);
lean_inc(v_val_4255_);
lean_dec_ref_known(v_a_4192_, 1);
if (lean_obj_tag(v_val_4255_) == 0)
{
lean_object* v_e_4256_; lean_object* v_o_4257_; lean_object* v_n_4258_; lean_object* v_n_4259_; uint8_t v___x_4260_; 
v_e_4256_ = lean_ctor_get(v_val_4190_, 0);
lean_inc_ref(v_e_4256_);
v_o_4257_ = lean_ctor_get(v_val_4190_, 1);
lean_inc_ref(v_o_4257_);
v_n_4258_ = lean_ctor_get(v_val_4190_, 2);
lean_inc(v_n_4258_);
lean_dec_ref_known(v_val_4190_, 3);
v_n_4259_ = lean_ctor_get(v_val_4255_, 0);
lean_inc(v_n_4259_);
lean_dec_ref_known(v_val_4255_, 1);
v___x_4260_ = lean_nat_dec_le(v_n_4258_, v_n_4259_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_dec(v_n_4259_);
lean_dec(v_n_4258_);
lean_inc_ref(v_o_4257_);
lean_inc_ref(v_y_4177_);
v___x_4261_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_4177_, v_o_4257_);
v___x_4262_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4261_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7));
v___x_4265_ = lean_unsigned_to_nat(4u);
v___x_4266_ = lean_mk_empty_array_with_capacity(v___x_4265_);
v___x_4267_ = lean_array_push(v___x_4266_, v_e_4256_);
v___x_4268_ = lean_array_push(v___x_4267_, v_o_4257_);
v___x_4269_ = lean_array_push(v___x_4268_, v_y_4177_);
v___x_4270_ = lean_array_push(v___x_4269_, v_a_4263_);
v___x_4271_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4183_, v___x_4264_, v___x_4270_, v_a_4181_);
lean_dec_ref(v___x_4270_);
return v___x_4271_;
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec_ref(v_o_4257_);
lean_dec_ref(v_e_4256_);
lean_dec_ref(v_y_4177_);
v_a_4272_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4262_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4262_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_object* v___f_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
lean_inc_ref(v_e_4256_);
v___f_4280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4280_, 0, v_n_4259_);
lean_closure_set(v___f_4280_, 1, v_n_4258_);
lean_closure_set(v___f_4280_, 2, v_e_4256_);
lean_inc_ref(v_y_4177_);
lean_inc_ref(v_o_4257_);
v___x_4281_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4257_, v_y_4177_);
v___x_4282_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4281_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9));
v___x_4285_ = lean_unsigned_to_nat(4u);
v___x_4286_ = lean_mk_empty_array_with_capacity(v___x_4285_);
v___x_4287_ = lean_array_push(v___x_4286_, v_e_4256_);
v___x_4288_ = lean_array_push(v___x_4287_, v_o_4257_);
v___x_4289_ = lean_array_push(v___x_4288_, v_y_4177_);
v___x_4290_ = lean_array_push(v___x_4289_, v_a_4283_);
v___x_4291_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4280_, v___x_4284_, v___x_4290_, v_a_4181_);
lean_dec_ref(v___x_4290_);
return v___x_4291_;
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v___f_4280_);
lean_dec_ref(v_o_4257_);
lean_dec_ref(v_e_4256_);
lean_dec_ref(v_y_4177_);
v_a_4292_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4282_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4282_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
else
{
lean_object* v_e_4300_; lean_object* v_o_4301_; lean_object* v_n_4302_; lean_object* v_e_4303_; lean_object* v_o_4304_; lean_object* v_n_4305_; lean_object* v___y_4307_; uint8_t v___x_4329_; 
lean_dec_ref(v_y_4177_);
v_e_4300_ = lean_ctor_get(v_val_4190_, 0);
lean_inc_ref(v_e_4300_);
v_o_4301_ = lean_ctor_get(v_val_4190_, 1);
lean_inc_ref(v_o_4301_);
v_n_4302_ = lean_ctor_get(v_val_4190_, 2);
lean_inc(v_n_4302_);
lean_dec_ref_known(v_val_4190_, 3);
v_e_4303_ = lean_ctor_get(v_val_4255_, 0);
lean_inc_ref(v_e_4303_);
v_o_4304_ = lean_ctor_get(v_val_4255_, 1);
lean_inc_ref(v_o_4304_);
v_n_4305_ = lean_ctor_get(v_val_4255_, 2);
lean_inc(v_n_4305_);
lean_dec_ref_known(v_val_4255_, 3);
v___x_4329_ = lean_nat_dec_le(v_n_4302_, v_n_4305_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___f_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4330_ = lean_nat_sub(v_n_4302_, v_n_4305_);
lean_dec(v_n_4305_);
lean_dec(v_n_4302_);
v___x_4331_ = l_Lean_mkNatLit(v___x_4330_);
lean_inc_ref(v_e_4300_);
v___x_4332_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4300_, v___x_4331_);
lean_inc_ref(v_e_4303_);
v___f_4333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__3), 3, 2);
lean_closure_set(v___f_4333_, 0, v___x_4332_);
lean_closure_set(v___f_4333_, 1, v_e_4303_);
lean_inc_ref(v_o_4301_);
lean_inc_ref(v_o_4304_);
v___x_4334_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4304_, v_o_4301_);
v___x_4335_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4334_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13));
v___x_4338_ = lean_unsigned_to_nat(5u);
v___x_4339_ = lean_mk_empty_array_with_capacity(v___x_4338_);
v___x_4340_ = lean_array_push(v___x_4339_, v_e_4300_);
v___x_4341_ = lean_array_push(v___x_4340_, v_e_4303_);
v___x_4342_ = lean_array_push(v___x_4341_, v_o_4301_);
v___x_4343_ = lean_array_push(v___x_4342_, v_o_4304_);
v___x_4344_ = lean_array_push(v___x_4343_, v_a_4336_);
v___x_4345_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4333_, v___x_4337_, v___x_4344_, v_a_4181_);
lean_dec_ref(v___x_4344_);
return v___x_4345_;
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec_ref(v___f_4333_);
lean_dec_ref(v_o_4304_);
lean_dec_ref(v_e_4303_);
lean_dec_ref(v_o_4301_);
lean_dec_ref(v_e_4300_);
v_a_4346_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4335_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4335_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
else
{
uint8_t v___x_4354_; 
v___x_4354_ = lean_nat_dec_eq(v_n_4302_, v_n_4305_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = lean_nat_sub(v_n_4305_, v_n_4302_);
lean_dec(v_n_4302_);
lean_dec(v_n_4305_);
v___x_4356_ = l_Lean_mkNatLit(v___x_4355_);
lean_inc_ref(v_e_4303_);
v___x_4357_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4303_, v___x_4356_);
v___y_4307_ = v___x_4357_;
goto v___jp_4306_;
}
else
{
lean_dec(v_n_4305_);
lean_dec(v_n_4302_);
lean_inc_ref(v_e_4303_);
v___y_4307_ = v_e_4303_;
goto v___jp_4306_;
}
}
v___jp_4306_:
{
lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_inc_ref(v_e_4300_);
v___f_4308_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4308_, 0, v_e_4300_);
lean_closure_set(v___f_4308_, 1, v___y_4307_);
lean_inc_ref(v_o_4304_);
lean_inc_ref(v_o_4301_);
v___x_4309_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4301_, v_o_4304_);
v___x_4310_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4309_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
v___x_4312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11));
v___x_4313_ = lean_unsigned_to_nat(5u);
v___x_4314_ = lean_mk_empty_array_with_capacity(v___x_4313_);
v___x_4315_ = lean_array_push(v___x_4314_, v_e_4300_);
v___x_4316_ = lean_array_push(v___x_4315_, v_e_4303_);
v___x_4317_ = lean_array_push(v___x_4316_, v_o_4301_);
v___x_4318_ = lean_array_push(v___x_4317_, v_o_4304_);
v___x_4319_ = lean_array_push(v___x_4318_, v_a_4311_);
v___x_4320_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4308_, v___x_4312_, v___x_4319_, v_a_4181_);
lean_dec_ref(v___x_4319_);
return v___x_4320_;
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec_ref(v___f_4308_);
lean_dec_ref(v_o_4304_);
lean_dec_ref(v_e_4303_);
lean_dec_ref(v_o_4301_);
lean_dec_ref(v_e_4300_);
v_a_4321_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4310_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4310_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4360_; 
lean_dec(v_a_4192_);
lean_dec(v_val_4190_);
lean_dec_ref(v_y_4177_);
lean_dec_ref(v_x_4176_);
v___x_4358_ = lean_box(0);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4358_);
v___x_4360_ = v___x_4194_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v_val_4190_);
lean_dec_ref(v_y_4177_);
lean_dec_ref(v_x_4176_);
v_a_4363_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4191_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4191_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4373_; 
lean_dec(v_a_4186_);
lean_dec_ref(v_y_4177_);
lean_dec_ref(v_x_4176_);
v___x_4371_ = lean_box(0);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___x_4371_);
v___x_4373_ = v___x_4188_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec_ref(v_y_4177_);
lean_dec_ref(v_x_4176_);
v_a_4376_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4185_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4185_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___boxed(lean_object* v_x_4384_, lean_object* v_y_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4384_, v_y_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr(lean_object* v_x_4392_, lean_object* v_y_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4392_, v_y_4393_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___boxed(lean_object* v_x_4403_, lean_object* v_y_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr(v_x_4403_, v_y_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_a_4405_);
return v_res_4413_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = lean_box(0);
v___x_4418_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__1));
v___x_4419_ = l_Lean_mkConst(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = lean_box(0);
v___x_4424_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__4));
v___x_4425_ = l_Lean_mkConst(v___x_4424_, v___x_4423_);
return v___x_4425_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__8(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4429_ = lean_box(0);
v___x_4430_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__7));
v___x_4431_ = l_Lean_mkConst(v___x_4430_, v___x_4429_);
return v___x_4431_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__11(void){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = lean_box(0);
v___x_4436_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__10));
v___x_4437_ = l_Lean_mkConst(v___x_4436_, v___x_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object* v_e_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; uint8_t v___x_4446_; 
v___x_4444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_4445_ = lean_unsigned_to_nat(3u);
v___x_4446_ = l_Lean_Expr_isAppOfArity(v_e_4438_, v___x_4444_, v___x_4445_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
lean_dec_ref(v_e_4438_);
v___x_4447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
return v___x_4448_;
}
else
{
lean_object* v___x_4449_; lean_object* v_x_4450_; lean_object* v_y_4451_; lean_object* v___x_4452_; 
v___x_4449_ = l_Lean_Expr_appFn_x21(v_e_4438_);
v_x_4450_ = l_Lean_Expr_appArg_x21(v___x_4449_);
lean_dec_ref(v___x_4449_);
v_y_4451_ = l_Lean_Expr_appArg_x21(v_e_4438_);
v___x_4452_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4450_, v_y_4451_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4577_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4455_ = v___x_4452_;
v_isShared_4456_ = v_isSharedCheck_4577_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4452_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4577_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
if (lean_obj_tag(v_a_4453_) == 0)
{
lean_object* v___x_4457_; lean_object* v___x_4459_; 
lean_dec_ref(v_e_4438_);
v___x_4457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4457_);
v___x_4459_ = v___x_4455_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
else
{
lean_object* v_val_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4576_; 
v_val_4461_ = lean_ctor_get(v_a_4453_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_a_4453_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4463_ = v_a_4453_;
v_isShared_4464_ = v_isSharedCheck_4576_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_val_4461_);
lean_dec(v_a_4453_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4576_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
switch(lean_obj_tag(v_val_4461_))
{
case 0:
{
uint8_t v_b_4465_; 
lean_del_object(v___x_4455_);
v_b_4465_ = lean_ctor_get_uint8(v_val_4461_, 0);
lean_dec_ref_known(v_val_4461_, 0);
if (v_b_4465_ == 0)
{
lean_object* v___x_4466_; 
lean_inc_ref(v_e_4438_);
v___x_4466_ = l_Lean_Meta_mkDecide(v_e_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v___x_4468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___x_4469_ = l_Lean_Meta_mkEqRefl(v___x_4468_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4490_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4472_ = v___x_4469_;
v_isShared_4473_ = v_isSharedCheck_4490_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4490_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4474_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__2, &l_Nat_reduceEqDiff___redArg___closed__2_once, _init_l_Nat_reduceEqDiff___redArg___closed__2);
v___x_4475_ = l_Lean_Expr_appArg_x21(v_a_4467_);
lean_dec(v_a_4467_);
v___x_4476_ = lean_mk_empty_array_with_capacity(v___x_4445_);
v___x_4477_ = lean_array_push(v___x_4476_, v_e_4438_);
v___x_4478_ = lean_array_push(v___x_4477_, v___x_4475_);
v___x_4479_ = lean_array_push(v___x_4478_, v_a_4470_);
v___x_4480_ = l_Lean_mkAppN(v___x_4474_, v___x_4479_);
lean_dec_ref(v___x_4479_);
v___x_4481_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4480_);
v___x_4483_ = v___x_4463_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4480_);
v___x_4483_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4487_; 
v___x_4484_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4484_, 0, v___x_4481_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
lean_ctor_set_uint8(v___x_4484_, sizeof(void*)*2, v___x_4446_);
v___x_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4485_);
v___x_4487_ = v___x_4472_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_a_4467_);
lean_del_object(v___x_4463_);
lean_dec_ref(v_e_4438_);
v_a_4491_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4469_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4469_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_del_object(v___x_4463_);
lean_dec_ref(v_e_4438_);
v_a_4499_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4466_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4466_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v___x_4507_; 
lean_inc_ref(v_e_4438_);
v___x_4507_ = l_Lean_Meta_mkDecide(v_e_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref_known(v___x_4507_, 1);
v___x_4509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___x_4510_ = l_Lean_Meta_mkEqRefl(v___x_4509_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4531_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4513_ = v___x_4510_;
v_isShared_4514_ = v_isSharedCheck_4531_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4510_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4531_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4524_; 
v___x_4515_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__8, &l_Nat_reduceEqDiff___redArg___closed__8_once, _init_l_Nat_reduceEqDiff___redArg___closed__8);
v___x_4516_ = l_Lean_Expr_appArg_x21(v_a_4508_);
lean_dec(v_a_4508_);
v___x_4517_ = lean_mk_empty_array_with_capacity(v___x_4445_);
v___x_4518_ = lean_array_push(v___x_4517_, v_e_4438_);
v___x_4519_ = lean_array_push(v___x_4518_, v___x_4516_);
v___x_4520_ = lean_array_push(v___x_4519_, v_a_4511_);
v___x_4521_ = l_Lean_mkAppN(v___x_4515_, v___x_4520_);
lean_dec_ref(v___x_4520_);
v___x_4522_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4521_);
v___x_4524_ = v___x_4463_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4521_);
v___x_4524_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4528_; 
v___x_4525_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4525_, 0, v___x_4522_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
lean_ctor_set_uint8(v___x_4525_, sizeof(void*)*2, v___x_4446_);
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4526_);
v___x_4528_ = v___x_4513_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4526_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
lean_dec(v_a_4508_);
lean_del_object(v___x_4463_);
lean_dec_ref(v_e_4438_);
v_a_4532_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4510_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4510_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_del_object(v___x_4463_);
lean_dec_ref(v_e_4438_);
v_a_4540_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4507_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4507_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
}
case 1:
{
lean_object* v_p_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4563_; 
lean_dec_ref(v_e_4438_);
v_p_4548_ = lean_ctor_get(v_val_4461_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_val_4461_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4550_ = v_val_4461_;
v_isShared_4551_ = v_isSharedCheck_4563_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_p_4548_);
lean_dec(v_val_4461_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4563_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4554_; 
v___x_4552_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v_p_4548_);
v___x_4554_ = v___x_4463_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_p_4548_);
v___x_4554_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4555_; lean_object* v___x_4557_; 
v___x_4555_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4555_, 0, v___x_4552_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
lean_ctor_set_uint8(v___x_4555_, sizeof(void*)*2, v___x_4446_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set_tag(v___x_4550_, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4555_);
v___x_4557_ = v___x_4550_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
lean_object* v___x_4559_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4557_);
v___x_4559_ = v___x_4455_;
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
}
}
}
default: 
{
lean_object* v_x_4564_; lean_object* v_y_4565_; lean_object* v_p_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
lean_dec_ref(v_e_4438_);
v_x_4564_ = lean_ctor_get(v_val_4461_, 0);
lean_inc_ref(v_x_4564_);
v_y_4565_ = lean_ctor_get(v_val_4461_, 1);
lean_inc_ref(v_y_4565_);
v_p_4566_ = lean_ctor_get(v_val_4461_, 2);
lean_inc_ref(v_p_4566_);
lean_dec_ref_known(v_val_4461_, 3);
v___x_4567_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(v_x_4564_, v_y_4565_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v_p_4566_);
v___x_4569_ = v___x_4463_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_p_4566_);
v___x_4569_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4573_; 
v___x_4570_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4570_, 0, v___x_4567_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
lean_ctor_set_uint8(v___x_4570_, sizeof(void*)*2, v___x_4446_);
v___x_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4570_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4571_);
v___x_4573_ = v___x_4455_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4571_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
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
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
lean_dec_ref(v_e_4438_);
v_a_4578_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4452_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4452_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg___boxed(lean_object* v_e_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Nat_reduceEqDiff___redArg(v_e_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object* v_e_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Nat_reduceEqDiff___redArg(v_e_4593_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object* v_e_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Nat_reduceEqDiff(v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_a_4604_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4632_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4633_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4630_, v___x_4631_, v___x_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27____boxed(lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_();
return v_res_4635_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_4639_; uint8_t v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4640_ = 1;
v___x_4641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_);
v___x_4642_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4639_, v___x_4640_, v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29____boxed(lean_object* v_a_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_();
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_4646_; uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4647_ = 1;
v___x_4648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_);
v___x_4649_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4646_, v___x_4647_, v___x_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31____boxed(lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_();
return v_res_4651_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = lean_box(0);
v___x_4658_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__1));
v___x_4659_ = l_Lean_mkConst(v___x_4658_, v___x_4657_);
return v___x_4659_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = lean_box(0);
v___x_4666_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__4));
v___x_4667_ = l_Lean_mkConst(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object* v_e_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v___x_4674_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_4675_ = lean_unsigned_to_nat(4u);
v___x_4676_ = l_Lean_Expr_isAppOfArity(v_e_4668_, v___x_4674_, v___x_4675_);
if (v___x_4676_ == 0)
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
return v___x_4678_;
}
else
{
lean_object* v___x_4679_; lean_object* v_x_4680_; lean_object* v_y_4681_; lean_object* v___x_4682_; 
v___x_4679_ = l_Lean_Expr_appFn_x21(v_e_4668_);
v_x_4680_ = l_Lean_Expr_appArg_x21(v___x_4679_);
lean_dec_ref(v___x_4679_);
v_y_4681_ = l_Lean_Expr_appArg_x21(v_e_4668_);
lean_inc_ref(v_y_4681_);
lean_inc_ref(v_x_4680_);
v___x_4682_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4680_, v_y_4681_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4745_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4745_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4745_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___y_4688_; 
if (lean_obj_tag(v_a_4683_) == 0)
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
lean_del_object(v___x_4685_);
lean_dec_ref(v_y_4681_);
lean_dec_ref(v_x_4680_);
v___x_4695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4695_);
return v___x_4696_;
}
else
{
lean_object* v_val_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4744_; 
v_val_4697_ = lean_ctor_get(v_a_4683_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v_a_4683_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4699_ = v_a_4683_;
v_isShared_4700_ = v_isSharedCheck_4744_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_val_4697_);
lean_dec(v_a_4683_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4744_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
switch(lean_obj_tag(v_val_4697_))
{
case 0:
{
uint8_t v_b_4701_; 
lean_del_object(v___x_4699_);
lean_dec_ref(v_y_4681_);
lean_dec_ref(v_x_4680_);
v_b_4701_ = lean_ctor_get_uint8(v_val_4697_, 0);
lean_dec_ref_known(v_val_4697_, 0);
if (v_b_4701_ == 0)
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_4688_ = v___x_4702_;
goto v___jp_4687_;
}
else
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___y_4688_ = v___x_4703_;
goto v___jp_4687_;
}
}
case 1:
{
lean_object* v_p_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4724_; 
lean_del_object(v___x_4685_);
v_p_4704_ = lean_ctor_get(v_val_4697_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_val_4697_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4706_ = v_val_4697_;
v_isShared_4707_ = v_isSharedCheck_4724_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_p_4704_);
lean_dec(v_val_4697_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4724_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
v___x_4708_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__2, &l_Nat_reduceBeqDiff___redArg___closed__2_once, _init_l_Nat_reduceBeqDiff___redArg___closed__2);
v___x_4709_ = lean_unsigned_to_nat(3u);
v___x_4710_ = lean_mk_empty_array_with_capacity(v___x_4709_);
v___x_4711_ = lean_array_push(v___x_4710_, v_x_4680_);
v___x_4712_ = lean_array_push(v___x_4711_, v_y_4681_);
v___x_4713_ = lean_array_push(v___x_4712_, v_p_4704_);
v___x_4714_ = l_Lean_mkAppN(v___x_4708_, v___x_4713_);
lean_dec_ref(v___x_4713_);
v___x_4715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v___x_4714_);
v___x_4717_ = v___x_4699_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4714_);
v___x_4717_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; lean_object* v___x_4720_; 
v___x_4718_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4718_, 0, v___x_4715_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
lean_ctor_set_uint8(v___x_4718_, sizeof(void*)*2, v___x_4676_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set_tag(v___x_4706_, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4718_);
v___x_4720_ = v___x_4706_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4718_);
v___x_4720_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; 
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
return v___x_4721_;
}
}
}
}
default: 
{
lean_object* v_x_4725_; lean_object* v_y_4726_; lean_object* v_p_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4739_; 
lean_del_object(v___x_4685_);
v_x_4725_ = lean_ctor_get(v_val_4697_, 0);
lean_inc_ref_n(v_x_4725_, 2);
v_y_4726_ = lean_ctor_get(v_val_4697_, 1);
lean_inc_ref_n(v_y_4726_, 2);
v_p_4727_ = lean_ctor_get(v_val_4697_, 2);
lean_inc_ref(v_p_4727_);
lean_dec_ref_known(v_val_4697_, 3);
v___x_4728_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__5, &l_Nat_reduceBeqDiff___redArg___closed__5_once, _init_l_Nat_reduceBeqDiff___redArg___closed__5);
v___x_4729_ = lean_unsigned_to_nat(5u);
v___x_4730_ = lean_mk_empty_array_with_capacity(v___x_4729_);
v___x_4731_ = lean_array_push(v___x_4730_, v_x_4680_);
v___x_4732_ = lean_array_push(v___x_4731_, v_y_4681_);
v___x_4733_ = lean_array_push(v___x_4732_, v_x_4725_);
v___x_4734_ = lean_array_push(v___x_4733_, v_y_4726_);
v___x_4735_ = lean_array_push(v___x_4734_, v_p_4727_);
v___x_4736_ = l_Lean_mkAppN(v___x_4728_, v___x_4735_);
lean_dec_ref(v___x_4735_);
v___x_4737_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(v_x_4725_, v_y_4726_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v___x_4736_);
v___x_4739_ = v___x_4699_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4736_);
v___x_4739_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4740_, 0, v___x_4737_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
lean_ctor_set_uint8(v___x_4740_, sizeof(void*)*2, v___x_4676_);
v___x_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
v___x_4742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
return v___x_4742_;
}
}
}
}
}
v___jp_4687_:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4693_; 
v___x_4689_ = lean_box(0);
lean_inc_ref(v___y_4688_);
v___x_4690_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4690_, 0, v___y_4688_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
lean_ctor_set_uint8(v___x_4690_, sizeof(void*)*2, v___x_4676_);
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4691_);
v___x_4693_ = v___x_4685_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_dec_ref(v_y_4681_);
lean_dec_ref(v_x_4680_);
v_a_4746_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4682_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4682_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object* v_e_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Nat_reduceBeqDiff___redArg(v_e_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec_ref(v_e_4754_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object* v_e_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Nat_reduceBeqDiff___redArg(v_e_4761_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object* v_e_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Nat_reduceBeqDiff(v_e_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_e_4771_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_));
v___x_4787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_4788_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4789_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4786_, v___x_4787_, v___x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27____boxed(lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_();
return v_res_4791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_4795_; uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_));
v___x_4796_ = 1;
v___x_4797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_);
v___x_4798_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4795_, v___x_4796_, v___x_4797_);
return v___x_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29____boxed(lean_object* v_a_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_();
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_));
v___x_4803_ = 1;
v___x_4804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_);
v___x_4805_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4802_, v___x_4803_, v___x_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31____boxed(lean_object* v_a_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_();
return v_res_4807_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = lean_box(0);
v___x_4814_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__1));
v___x_4815_ = l_Lean_mkConst(v___x_4814_, v___x_4813_);
return v___x_4815_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = lean_box(0);
v___x_4822_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__4));
v___x_4823_ = l_Lean_mkConst(v___x_4822_, v___x_4821_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object* v_e_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4830_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_4831_ = lean_unsigned_to_nat(4u);
v___x_4832_ = l_Lean_Expr_isAppOfArity(v_e_4824_, v___x_4830_, v___x_4831_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
return v___x_4834_;
}
else
{
lean_object* v___x_4835_; lean_object* v_x_4836_; lean_object* v_y_4837_; lean_object* v___x_4838_; 
v___x_4835_ = l_Lean_Expr_appFn_x21(v_e_4824_);
v_x_4836_ = l_Lean_Expr_appArg_x21(v___x_4835_);
lean_dec_ref(v___x_4835_);
v_y_4837_ = l_Lean_Expr_appArg_x21(v_e_4824_);
lean_inc_ref(v_y_4837_);
lean_inc_ref(v_x_4836_);
v___x_4838_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4836_, v_y_4837_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4901_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4841_ = v___x_4838_;
v_isShared_4842_ = v_isSharedCheck_4901_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4838_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4901_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___y_4844_; 
if (lean_obj_tag(v_a_4839_) == 0)
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
lean_del_object(v___x_4841_);
lean_dec_ref(v_y_4837_);
lean_dec_ref(v_x_4836_);
v___x_4851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
return v___x_4852_;
}
else
{
lean_object* v_val_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4900_; 
v_val_4853_ = lean_ctor_get(v_a_4839_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v_a_4839_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4855_ = v_a_4839_;
v_isShared_4856_ = v_isSharedCheck_4900_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_val_4853_);
lean_dec(v_a_4839_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4900_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
switch(lean_obj_tag(v_val_4853_))
{
case 0:
{
uint8_t v_b_4857_; 
lean_del_object(v___x_4855_);
lean_dec_ref(v_y_4837_);
lean_dec_ref(v_x_4836_);
v_b_4857_ = lean_ctor_get_uint8(v_val_4853_, 0);
lean_dec_ref_known(v_val_4853_, 0);
if (v_b_4857_ == 0)
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___y_4844_ = v___x_4858_;
goto v___jp_4843_;
}
else
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_4844_ = v___x_4859_;
goto v___jp_4843_;
}
}
case 1:
{
lean_object* v_p_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4880_; 
lean_del_object(v___x_4841_);
v_p_4860_ = lean_ctor_get(v_val_4853_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v_val_4853_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4862_ = v_val_4853_;
v_isShared_4863_ = v_isSharedCheck_4880_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_p_4860_);
lean_dec(v_val_4853_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4880_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4864_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__2, &l_Nat_reduceBneDiff___redArg___closed__2_once, _init_l_Nat_reduceBneDiff___redArg___closed__2);
v___x_4865_ = lean_unsigned_to_nat(3u);
v___x_4866_ = lean_mk_empty_array_with_capacity(v___x_4865_);
v___x_4867_ = lean_array_push(v___x_4866_, v_x_4836_);
v___x_4868_ = lean_array_push(v___x_4867_, v_y_4837_);
v___x_4869_ = lean_array_push(v___x_4868_, v_p_4860_);
v___x_4870_ = l_Lean_mkAppN(v___x_4864_, v___x_4869_);
lean_dec_ref(v___x_4869_);
v___x_4871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 0, v___x_4870_);
v___x_4873_ = v___x_4855_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4870_);
v___x_4873_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4874_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4874_, 0, v___x_4871_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
lean_ctor_set_uint8(v___x_4874_, sizeof(void*)*2, v___x_4832_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set_tag(v___x_4862_, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4874_);
v___x_4876_ = v___x_4862_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
}
}
}
default: 
{
lean_object* v_x_4881_; lean_object* v_y_4882_; lean_object* v_p_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
lean_del_object(v___x_4841_);
v_x_4881_ = lean_ctor_get(v_val_4853_, 0);
lean_inc_ref_n(v_x_4881_, 2);
v_y_4882_ = lean_ctor_get(v_val_4853_, 1);
lean_inc_ref_n(v_y_4882_, 2);
v_p_4883_ = lean_ctor_get(v_val_4853_, 2);
lean_inc_ref(v_p_4883_);
lean_dec_ref_known(v_val_4853_, 3);
v___x_4884_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__5, &l_Nat_reduceBneDiff___redArg___closed__5_once, _init_l_Nat_reduceBneDiff___redArg___closed__5);
v___x_4885_ = lean_unsigned_to_nat(5u);
v___x_4886_ = lean_mk_empty_array_with_capacity(v___x_4885_);
v___x_4887_ = lean_array_push(v___x_4886_, v_x_4836_);
v___x_4888_ = lean_array_push(v___x_4887_, v_y_4837_);
v___x_4889_ = lean_array_push(v___x_4888_, v_x_4881_);
v___x_4890_ = lean_array_push(v___x_4889_, v_y_4882_);
v___x_4891_ = lean_array_push(v___x_4890_, v_p_4883_);
v___x_4892_ = l_Lean_mkAppN(v___x_4884_, v___x_4891_);
lean_dec_ref(v___x_4891_);
v___x_4893_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(v_x_4881_, v_y_4882_);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 0, v___x_4892_);
v___x_4895_ = v___x_4855_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4892_);
v___x_4895_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4896_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4896_, 0, v___x_4893_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
lean_ctor_set_uint8(v___x_4896_, sizeof(void*)*2, v___x_4832_);
v___x_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
return v___x_4898_;
}
}
}
}
}
v___jp_4843_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4845_ = lean_box(0);
lean_inc_ref(v___y_4844_);
v___x_4846_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4846_, 0, v___y_4844_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
lean_ctor_set_uint8(v___x_4846_, sizeof(void*)*2, v___x_4832_);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 0, v___x_4847_);
v___x_4849_ = v___x_4841_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_dec_ref(v_y_4837_);
lean_dec_ref(v_x_4836_);
v_a_4902_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4838_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4838_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
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
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object* v_e_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Nat_reduceBneDiff___redArg(v_e_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec_ref(v_e_4910_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object* v_e_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Nat_reduceBneDiff___redArg(v_e_4917_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object* v_e_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Nat_reduceBneDiff(v_e_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
lean_dec(v_a_4934_);
lean_dec_ref(v_a_4933_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_e_4927_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_));
v___x_4943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_4944_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4945_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4942_, v___x_4943_, v___x_4944_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27____boxed(lean_object* v_a_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_();
return v_res_4947_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4948_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_4951_; uint8_t v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_));
v___x_4952_ = 1;
v___x_4953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_);
v___x_4954_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4951_, v___x_4952_, v___x_4953_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29____boxed(lean_object* v_a_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_();
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_4958_; uint8_t v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_));
v___x_4959_ = 1;
v___x_4960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_);
v___x_4961_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4958_, v___x_4959_, v___x_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31____boxed(lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_();
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(lean_object* v_nm_4994_, lean_object* v_arity_4995_, uint8_t v_isLT_4996_, lean_object* v_e_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v___y_5008_; uint8_t v___x_5030_; 
v___x_5030_ = l_Lean_Expr_isAppOfArity(v_e_4997_, v_nm_4994_, v_arity_4995_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
lean_dec_ref(v_e_4997_);
v___x_5031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5031_);
return v___x_5032_;
}
else
{
lean_object* v___x_5033_; lean_object* v_x_5034_; lean_object* v_y_5035_; lean_object* v___y_5037_; 
v___x_5033_ = l_Lean_Expr_appFn_x21(v_e_4997_);
v_x_5034_ = l_Lean_Expr_appArg_x21(v___x_5033_);
lean_dec_ref(v___x_5033_);
v_y_5035_ = l_Lean_Expr_appArg_x21(v_e_4997_);
if (v_isLT_4996_ == 0)
{
lean_object* v___x_5211_; 
v___x_5211_ = lean_unsigned_to_nat(0u);
v___y_5037_ = v___x_5211_;
goto v___jp_5036_;
}
else
{
lean_object* v___x_5212_; 
v___x_5212_ = lean_unsigned_to_nat(1u);
v___y_5037_ = v___x_5212_;
goto v___jp_5036_;
}
v___jp_5036_:
{
lean_object* v___x_5038_; 
lean_inc_ref(v_x_5034_);
v___x_5038_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_5034_, v___y_5037_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5202_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5041_ = v___x_5038_;
v_isShared_5042_ = v_isSharedCheck_5202_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5038_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5202_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
if (lean_obj_tag(v_a_5039_) == 1)
{
lean_object* v_val_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
lean_del_object(v___x_5041_);
v_val_5043_ = lean_ctor_get(v_a_5039_, 0);
lean_inc(v_val_5043_);
lean_dec_ref_known(v_a_5039_, 1);
v___x_5044_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_y_5035_);
v___x_5045_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_5035_, v___x_5044_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5189_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5048_ = v___x_5045_;
v_isShared_5049_ = v_isSharedCheck_5189_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5045_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5189_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
if (lean_obj_tag(v_a_5046_) == 1)
{
lean_del_object(v___x_5048_);
if (lean_obj_tag(v_val_5043_) == 0)
{
lean_object* v_val_5050_; 
lean_dec_ref(v_y_5035_);
v_val_5050_ = lean_ctor_get(v_a_5046_, 0);
lean_inc(v_val_5050_);
lean_dec_ref_known(v_a_5046_, 1);
if (lean_obj_tag(v_val_5050_) == 0)
{
lean_object* v_n_5051_; lean_object* v_n_5052_; uint8_t v___x_5053_; lean_object* v___x_5054_; 
lean_dec_ref(v_x_5034_);
v_n_5051_ = lean_ctor_get(v_val_5043_, 0);
lean_inc(v_n_5051_);
lean_dec_ref_known(v_val_5043_, 1);
v_n_5052_ = lean_ctor_get(v_val_5050_, 0);
lean_inc(v_n_5052_);
lean_dec_ref_known(v_val_5050_, 1);
v___x_5053_ = lean_nat_dec_le(v_n_5051_, v_n_5052_);
lean_dec(v_n_5052_);
lean_dec(v_n_5051_);
v___x_5054_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_4997_, v___x_5053_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5054_;
}
else
{
lean_object* v_n_5055_; lean_object* v_e_5056_; lean_object* v_o_5057_; lean_object* v_n_5058_; uint8_t v___x_5059_; 
lean_dec_ref(v_e_4997_);
v_n_5055_ = lean_ctor_get(v_val_5043_, 0);
lean_inc(v_n_5055_);
lean_dec_ref_known(v_val_5043_, 1);
v_e_5056_ = lean_ctor_get(v_val_5050_, 0);
lean_inc_ref(v_e_5056_);
v_o_5057_ = lean_ctor_get(v_val_5050_, 1);
lean_inc_ref(v_o_5057_);
v_n_5058_ = lean_ctor_get(v_val_5050_, 2);
lean_inc(v_n_5058_);
lean_dec_ref_known(v_val_5050_, 3);
v___x_5059_ = lean_nat_dec_le(v_n_5055_, v_n_5058_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5060_ = lean_nat_sub(v_n_5055_, v_n_5058_);
lean_dec(v_n_5058_);
lean_dec(v_n_5055_);
v___x_5061_ = l_Lean_mkNatLit(v___x_5060_);
lean_inc_ref(v_e_5056_);
v___x_5062_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_5061_, v_e_5056_);
lean_inc_ref(v_x_5034_);
lean_inc_ref(v_o_5057_);
v___x_5063_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5057_, v_x_5034_);
v___x_5064_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5063_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v___x_5064_, 1);
v___x_5066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3));
v___x_5067_ = lean_unsigned_to_nat(4u);
v___x_5068_ = lean_mk_empty_array_with_capacity(v___x_5067_);
v___x_5069_ = lean_array_push(v___x_5068_, v_x_5034_);
v___x_5070_ = lean_array_push(v___x_5069_, v_e_5056_);
v___x_5071_ = lean_array_push(v___x_5070_, v_o_5057_);
v___x_5072_ = lean_array_push(v___x_5071_, v_a_5065_);
v___x_5073_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5062_, v___x_5066_, v___x_5072_, v_a_5001_);
lean_dec_ref(v___x_5072_);
return v___x_5073_;
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5081_; 
lean_dec_ref(v___x_5062_);
lean_dec_ref(v_o_5057_);
lean_dec_ref(v_e_5056_);
lean_dec_ref(v_x_5034_);
v_a_5074_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_5064_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5064_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
else
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
lean_dec(v_n_5058_);
lean_dec(v_n_5055_);
lean_inc_ref(v_o_5057_);
lean_inc_ref(v_x_5034_);
v___x_5082_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_x_5034_, v_o_5057_);
v___x_5083_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5082_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5084_);
lean_dec_ref_known(v___x_5083_, 1);
v___x_5085_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_5086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5));
v___x_5087_ = lean_unsigned_to_nat(4u);
v___x_5088_ = lean_mk_empty_array_with_capacity(v___x_5087_);
v___x_5089_ = lean_array_push(v___x_5088_, v_x_5034_);
v___x_5090_ = lean_array_push(v___x_5089_, v_e_5056_);
v___x_5091_ = lean_array_push(v___x_5090_, v_o_5057_);
v___x_5092_ = lean_array_push(v___x_5091_, v_a_5084_);
v___x_5093_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5085_, v___x_5086_, v___x_5092_, v_a_5001_);
lean_dec_ref(v___x_5092_);
return v___x_5093_;
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec_ref(v_o_5057_);
lean_dec_ref(v_e_5056_);
lean_dec_ref(v_x_5034_);
v_a_5094_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5083_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5083_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
}
}
else
{
lean_object* v_val_5102_; 
lean_dec_ref(v_x_5034_);
lean_dec_ref(v_e_4997_);
v_val_5102_ = lean_ctor_get(v_a_5046_, 0);
lean_inc(v_val_5102_);
lean_dec_ref_known(v_a_5046_, 1);
if (lean_obj_tag(v_val_5102_) == 0)
{
lean_object* v_e_5103_; lean_object* v_o_5104_; lean_object* v_n_5105_; lean_object* v_n_5106_; uint8_t v___x_5107_; 
v_e_5103_ = lean_ctor_get(v_val_5043_, 0);
lean_inc_ref(v_e_5103_);
v_o_5104_ = lean_ctor_get(v_val_5043_, 1);
lean_inc_ref(v_o_5104_);
v_n_5105_ = lean_ctor_get(v_val_5043_, 2);
lean_inc(v_n_5105_);
lean_dec_ref_known(v_val_5043_, 3);
v_n_5106_ = lean_ctor_get(v_val_5102_, 0);
lean_inc(v_n_5106_);
lean_dec_ref_known(v_val_5102_, 1);
v___x_5107_ = lean_nat_dec_le(v_n_5105_, v_n_5106_);
if (v___x_5107_ == 0)
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_dec(v_n_5106_);
lean_dec(v_n_5105_);
lean_inc_ref(v_o_5104_);
lean_inc_ref(v_y_5035_);
v___x_5108_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_5035_, v_o_5104_);
v___x_5109_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5108_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v_a_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_a_5110_);
lean_dec_ref_known(v___x_5109_, 1);
v___x_5111_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_5112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7));
v___x_5113_ = lean_unsigned_to_nat(4u);
v___x_5114_ = lean_mk_empty_array_with_capacity(v___x_5113_);
v___x_5115_ = lean_array_push(v___x_5114_, v_e_5103_);
v___x_5116_ = lean_array_push(v___x_5115_, v_o_5104_);
v___x_5117_ = lean_array_push(v___x_5116_, v_y_5035_);
v___x_5118_ = lean_array_push(v___x_5117_, v_a_5110_);
v___x_5119_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5111_, v___x_5112_, v___x_5118_, v_a_5001_);
lean_dec_ref(v___x_5118_);
return v___x_5119_;
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_dec_ref(v_o_5104_);
lean_dec_ref(v_e_5103_);
lean_dec_ref(v_y_5035_);
v_a_5120_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5109_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5109_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
}
else
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5128_ = lean_nat_sub(v_n_5106_, v_n_5105_);
lean_dec(v_n_5105_);
lean_dec(v_n_5106_);
v___x_5129_ = l_Lean_mkNatLit(v___x_5128_);
lean_inc_ref(v_e_5103_);
v___x_5130_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_e_5103_, v___x_5129_);
lean_inc_ref(v_y_5035_);
lean_inc_ref(v_o_5104_);
v___x_5131_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5104_, v_y_5035_);
v___x_5132_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5131_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___x_5134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9));
v___x_5135_ = lean_unsigned_to_nat(4u);
v___x_5136_ = lean_mk_empty_array_with_capacity(v___x_5135_);
v___x_5137_ = lean_array_push(v___x_5136_, v_e_5103_);
v___x_5138_ = lean_array_push(v___x_5137_, v_o_5104_);
v___x_5139_ = lean_array_push(v___x_5138_, v_y_5035_);
v___x_5140_ = lean_array_push(v___x_5139_, v_a_5133_);
v___x_5141_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5130_, v___x_5134_, v___x_5140_, v_a_5001_);
lean_dec_ref(v___x_5140_);
return v___x_5141_;
}
else
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
lean_dec_ref(v___x_5130_);
lean_dec_ref(v_o_5104_);
lean_dec_ref(v_e_5103_);
lean_dec_ref(v_y_5035_);
v_a_5142_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5132_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5132_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
if (v_isShared_5145_ == 0)
{
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_a_5142_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
}
else
{
lean_object* v_e_5150_; lean_object* v_o_5151_; lean_object* v_n_5152_; lean_object* v_e_5153_; lean_object* v_o_5154_; lean_object* v_n_5155_; uint8_t v___x_5156_; 
lean_dec_ref(v_y_5035_);
v_e_5150_ = lean_ctor_get(v_val_5043_, 0);
lean_inc_ref(v_e_5150_);
v_o_5151_ = lean_ctor_get(v_val_5043_, 1);
lean_inc_ref(v_o_5151_);
v_n_5152_ = lean_ctor_get(v_val_5043_, 2);
lean_inc(v_n_5152_);
lean_dec_ref_known(v_val_5043_, 3);
v_e_5153_ = lean_ctor_get(v_val_5102_, 0);
lean_inc_ref(v_e_5153_);
v_o_5154_ = lean_ctor_get(v_val_5102_, 1);
lean_inc_ref(v_o_5154_);
v_n_5155_ = lean_ctor_get(v_val_5102_, 2);
lean_inc(v_n_5155_);
lean_dec_ref_known(v_val_5102_, 3);
v___x_5156_ = lean_nat_dec_le(v_n_5152_, v_n_5155_);
if (v___x_5156_ == 0)
{
lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5157_ = lean_nat_sub(v_n_5152_, v_n_5155_);
lean_dec(v_n_5155_);
lean_dec(v_n_5152_);
v___x_5158_ = l_Lean_mkNatLit(v___x_5157_);
lean_inc_ref(v_e_5150_);
v___x_5159_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5150_, v___x_5158_);
lean_inc_ref(v_e_5153_);
v___x_5160_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_5159_, v_e_5153_);
lean_inc_ref(v_o_5151_);
lean_inc_ref(v_o_5154_);
v___x_5161_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5154_, v_o_5151_);
v___x_5162_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5161_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v___x_5164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11));
v___x_5165_ = lean_unsigned_to_nat(5u);
v___x_5166_ = lean_mk_empty_array_with_capacity(v___x_5165_);
v___x_5167_ = lean_array_push(v___x_5166_, v_e_5150_);
v___x_5168_ = lean_array_push(v___x_5167_, v_e_5153_);
v___x_5169_ = lean_array_push(v___x_5168_, v_o_5151_);
v___x_5170_ = lean_array_push(v___x_5169_, v_o_5154_);
v___x_5171_ = lean_array_push(v___x_5170_, v_a_5163_);
v___x_5172_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5160_, v___x_5164_, v___x_5171_, v_a_5001_);
lean_dec_ref(v___x_5171_);
return v___x_5172_;
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec_ref(v___x_5160_);
lean_dec_ref(v_o_5154_);
lean_dec_ref(v_e_5153_);
lean_dec_ref(v_o_5151_);
lean_dec_ref(v_e_5150_);
v_a_5173_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5162_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5162_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
else
{
uint8_t v___x_5181_; 
v___x_5181_ = lean_nat_dec_eq(v_n_5152_, v_n_5155_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5182_ = lean_nat_sub(v_n_5155_, v_n_5152_);
lean_dec(v_n_5152_);
lean_dec(v_n_5155_);
v___x_5183_ = l_Lean_mkNatLit(v___x_5182_);
lean_inc_ref(v_e_5153_);
v___x_5184_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5153_, v___x_5183_);
v___y_5004_ = v_o_5154_;
v___y_5005_ = v_o_5151_;
v___y_5006_ = v_e_5150_;
v___y_5007_ = v_e_5153_;
v___y_5008_ = v___x_5184_;
goto v___jp_5003_;
}
else
{
lean_dec(v_n_5155_);
lean_dec(v_n_5152_);
lean_inc_ref(v_e_5153_);
v___y_5004_ = v_o_5154_;
v___y_5005_ = v_o_5151_;
v___y_5006_ = v_e_5150_;
v___y_5007_ = v_e_5153_;
v___y_5008_ = v_e_5153_;
goto v___jp_5003_;
}
}
}
}
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5187_; 
lean_dec(v_a_5046_);
lean_dec(v_val_5043_);
lean_dec_ref(v_y_5035_);
lean_dec_ref(v_x_5034_);
lean_dec_ref(v_e_4997_);
v___x_5185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 0, v___x_5185_);
v___x_5187_ = v___x_5048_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_val_5043_);
lean_dec_ref(v_y_5035_);
lean_dec_ref(v_x_5034_);
lean_dec_ref(v_e_4997_);
v_a_5190_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5045_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5045_);
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
lean_object* v___x_5198_; lean_object* v___x_5200_; 
lean_dec(v_a_5039_);
lean_dec_ref(v_y_5035_);
lean_dec_ref(v_x_5034_);
lean_dec_ref(v_e_4997_);
v___x_5198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5198_);
v___x_5200_ = v___x_5041_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
lean_dec_ref(v_y_5035_);
lean_dec_ref(v_x_5034_);
lean_dec_ref(v_e_4997_);
v_a_5203_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5038_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5038_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
v___jp_5003_:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
lean_inc_ref(v___y_5006_);
v___x_5009_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_5006_, v___y_5008_);
lean_inc_ref(v___y_5004_);
lean_inc_ref(v___y_5005_);
v___x_5010_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_5005_, v___y_5004_);
v___x_5011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5010_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5012_);
lean_dec_ref_known(v___x_5011_, 1);
v___x_5013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1));
v___x_5014_ = lean_unsigned_to_nat(5u);
v___x_5015_ = lean_mk_empty_array_with_capacity(v___x_5014_);
v___x_5016_ = lean_array_push(v___x_5015_, v___y_5006_);
v___x_5017_ = lean_array_push(v___x_5016_, v___y_5007_);
v___x_5018_ = lean_array_push(v___x_5017_, v___y_5005_);
v___x_5019_ = lean_array_push(v___x_5018_, v___y_5004_);
v___x_5020_ = lean_array_push(v___x_5019_, v_a_5012_);
v___x_5021_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5009_, v___x_5013_, v___x_5020_, v_a_5001_);
lean_dec_ref(v___x_5020_);
return v___x_5021_;
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_dec_ref(v___x_5009_);
lean_dec_ref(v___y_5007_);
lean_dec_ref(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec_ref(v___y_5004_);
v_a_5022_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5011_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5011_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___boxed(lean_object* v_nm_5213_, lean_object* v_arity_5214_, lean_object* v_isLT_5215_, lean_object* v_e_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_){
_start:
{
uint8_t v_isLT_boxed_5222_; lean_object* v_res_5223_; 
v_isLT_boxed_5222_ = lean_unbox(v_isLT_5215_);
v_res_5223_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(v_nm_5213_, v_arity_5214_, v_isLT_boxed_5222_, v_e_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec(v_a_5218_);
lean_dec_ref(v_a_5217_);
lean_dec(v_nm_5213_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE(lean_object* v_nm_5224_, lean_object* v_arity_5225_, uint8_t v_isLT_5226_, lean_object* v_e_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_){
_start:
{
lean_object* v___x_5236_; 
v___x_5236_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(v_nm_5224_, v_arity_5225_, v_isLT_5226_, v_e_5227_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___boxed(lean_object* v_nm_5237_, lean_object* v_arity_5238_, lean_object* v_isLT_5239_, lean_object* v_e_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_){
_start:
{
uint8_t v_isLT_boxed_5249_; lean_object* v_res_5250_; 
v_isLT_boxed_5249_ = lean_unbox(v_isLT_5239_);
v_res_5250_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE(v_nm_5237_, v_arity_5238_, v_isLT_boxed_5249_, v_e_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec(v_a_5241_);
lean_dec(v_nm_5237_);
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object* v_e_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v___x_5257_; lean_object* v___x_5258_; uint8_t v___x_5259_; lean_object* v___x_5260_; 
v___x_5257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_5258_ = lean_unsigned_to_nat(4u);
v___x_5259_ = 0;
v___x_5260_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(v___x_5257_, v___x_5258_, v___x_5259_, v_e_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg___boxed(lean_object* v_e_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Nat_reduceLeDiff___redArg(v_e_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object* v_e_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_){
_start:
{
lean_object* v___x_5277_; 
v___x_5277_ = l_Nat_reduceLeDiff___redArg(v_e_5268_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object* v_e_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Nat_reduceLeDiff(v_e_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
lean_dec(v_a_5285_);
lean_dec_ref(v_a_5284_);
lean_dec(v_a_5283_);
lean_dec_ref(v_a_5282_);
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5308_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5309_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5306_, v___x_5307_, v___x_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27____boxed(lean_object* v_a_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_();
return v_res_5311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5312_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_5315_; uint8_t v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5316_ = 1;
v___x_5317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_);
v___x_5318_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5315_, v___x_5316_, v___x_5317_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29____boxed(lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_();
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_5322_; uint8_t v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5323_ = 1;
v___x_5324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_);
v___x_5325_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5322_, v___x_5323_, v___x_5324_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31____boxed(lean_object* v_a_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_();
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object* v_e_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; 
v___x_5358_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_5359_ = lean_unsigned_to_nat(6u);
v___x_5360_ = l_Lean_Expr_isAppOfArity(v_e_5352_, v___x_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5362_, 0, v___x_5361_);
return v___x_5362_;
}
else
{
lean_object* v___x_5363_; lean_object* v_p_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5363_ = l_Lean_Expr_appFn_x21(v_e_5352_);
v_p_5364_ = l_Lean_Expr_appArg_x21(v___x_5363_);
lean_dec_ref(v___x_5363_);
v___x_5365_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_5364_);
v___x_5366_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_p_5364_, v___x_5365_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5554_; 
v_a_5367_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5369_ = v___x_5366_;
v_isShared_5370_ = v_isSharedCheck_5554_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5366_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5554_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
if (lean_obj_tag(v_a_5367_) == 1)
{
lean_object* v_val_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
lean_del_object(v___x_5369_);
v_val_5371_ = lean_ctor_get(v_a_5367_, 0);
lean_inc(v_val_5371_);
lean_dec_ref_known(v_a_5367_, 1);
v___x_5372_ = l_Lean_Expr_appArg_x21(v_e_5352_);
lean_inc_ref(v___x_5372_);
v___x_5373_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v___x_5372_, v___x_5365_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5541_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5376_ = v___x_5373_;
v_isShared_5377_ = v_isSharedCheck_5541_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5541_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
if (lean_obj_tag(v_a_5374_) == 1)
{
lean_del_object(v___x_5376_);
if (lean_obj_tag(v_val_5371_) == 0)
{
lean_object* v_val_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5428_; 
lean_dec_ref(v___x_5372_);
v_val_5378_ = lean_ctor_get(v_a_5374_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v_a_5374_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5380_ = v_a_5374_;
v_isShared_5381_ = v_isSharedCheck_5428_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_val_5378_);
lean_dec(v_a_5374_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5428_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
if (lean_obj_tag(v_val_5378_) == 0)
{
lean_object* v_n_5382_; lean_object* v_n_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5413_; 
lean_dec_ref(v_p_5364_);
v_n_5382_ = lean_ctor_get(v_val_5371_, 0);
lean_inc(v_n_5382_);
lean_dec_ref_known(v_val_5371_, 1);
v_n_5383_ = lean_ctor_get(v_val_5378_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v_val_5378_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5385_ = v_val_5378_;
v_isShared_5386_ = v_isSharedCheck_5413_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_n_5383_);
lean_dec(v_val_5378_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5413_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5387_ = lean_nat_sub(v_n_5382_, v_n_5383_);
lean_dec(v_n_5383_);
lean_dec(v_n_5382_);
v___x_5388_ = l_Lean_mkNatLit(v___x_5387_);
lean_inc_ref(v___x_5388_);
v___x_5389_ = l_Lean_Meta_mkEqRefl(v___x_5388_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5404_; 
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5392_ = v___x_5389_;
v_isShared_5393_ = v_isSharedCheck_5404_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5389_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5404_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5395_; 
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 0, v_a_5390_);
v___x_5395_ = v___x_5380_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5390_);
v___x_5395_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5396_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5396_, 0, v___x_5388_);
lean_ctor_set(v___x_5396_, 1, v___x_5395_);
lean_ctor_set_uint8(v___x_5396_, sizeof(void*)*2, v___x_5360_);
if (v_isShared_5386_ == 0)
{
lean_ctor_set(v___x_5385_, 0, v___x_5396_);
v___x_5398_ = v___x_5385_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5396_);
v___x_5398_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
lean_object* v___x_5400_; 
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 0, v___x_5398_);
v___x_5400_ = v___x_5392_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
}
else
{
lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5412_; 
lean_dec_ref(v___x_5388_);
lean_del_object(v___x_5385_);
lean_del_object(v___x_5380_);
v_a_5405_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5412_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5407_ = v___x_5389_;
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_dec(v___x_5389_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5410_; 
if (v_isShared_5408_ == 0)
{
v___x_5410_ = v___x_5407_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
}
}
else
{
lean_object* v_n_5414_; lean_object* v_e_5415_; lean_object* v_o_5416_; lean_object* v_n_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; 
lean_del_object(v___x_5380_);
v_n_5414_ = lean_ctor_get(v_val_5371_, 0);
lean_inc(v_n_5414_);
lean_dec_ref_known(v_val_5371_, 1);
v_e_5415_ = lean_ctor_get(v_val_5378_, 0);
lean_inc_ref_n(v_e_5415_, 2);
v_o_5416_ = lean_ctor_get(v_val_5378_, 1);
lean_inc_ref(v_o_5416_);
v_n_5417_ = lean_ctor_get(v_val_5378_, 2);
lean_inc(v_n_5417_);
lean_dec_ref_known(v_val_5378_, 3);
v___x_5418_ = lean_nat_sub(v_n_5414_, v_n_5417_);
lean_dec(v_n_5417_);
lean_dec(v_n_5414_);
v___x_5419_ = l_Lean_mkNatLit(v___x_5418_);
v___x_5420_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5419_, v_e_5415_);
v___x_5421_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__1));
v___x_5422_ = lean_unsigned_to_nat(3u);
v___x_5423_ = lean_mk_empty_array_with_capacity(v___x_5422_);
v___x_5424_ = lean_array_push(v___x_5423_, v_p_5364_);
v___x_5425_ = lean_array_push(v___x_5424_, v_e_5415_);
v___x_5426_ = lean_array_push(v___x_5425_, v_o_5416_);
v___x_5427_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5420_, v___x_5421_, v___x_5426_, v_a_5356_);
lean_dec_ref(v___x_5426_);
return v___x_5427_;
}
}
}
else
{
lean_object* v_val_5429_; lean_object* v_e_5430_; lean_object* v_o_5431_; lean_object* v_n_5432_; lean_object* v___y_5434_; 
lean_dec_ref(v_p_5364_);
v_val_5429_ = lean_ctor_get(v_a_5374_, 0);
lean_inc(v_val_5429_);
lean_dec_ref_known(v_a_5374_, 1);
v_e_5430_ = lean_ctor_get(v_val_5371_, 0);
lean_inc_ref(v_e_5430_);
v_o_5431_ = lean_ctor_get(v_val_5371_, 1);
lean_inc_ref(v_o_5431_);
v_n_5432_ = lean_ctor_get(v_val_5371_, 2);
lean_inc(v_n_5432_);
lean_dec_ref_known(v_val_5371_, 3);
if (lean_obj_tag(v_val_5429_) == 0)
{
lean_object* v_n_5454_; uint8_t v___x_5455_; 
v_n_5454_ = lean_ctor_get(v_val_5429_, 0);
lean_inc(v_n_5454_);
lean_dec_ref_known(v_val_5429_, 1);
v___x_5455_ = lean_nat_dec_le(v_n_5432_, v_n_5454_);
if (v___x_5455_ == 0)
{
lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5456_ = lean_nat_sub(v_n_5432_, v_n_5454_);
lean_dec(v_n_5454_);
lean_dec(v_n_5432_);
v___x_5457_ = l_Lean_mkNatLit(v___x_5456_);
lean_inc_ref(v_e_5430_);
v___x_5458_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5430_, v___x_5457_);
lean_inc_ref(v_o_5431_);
lean_inc_ref(v___x_5372_);
v___x_5459_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_5372_, v_o_5431_);
v___x_5460_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5459_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref_known(v___x_5460_, 1);
v___x_5462_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__5));
v___x_5463_ = lean_unsigned_to_nat(4u);
v___x_5464_ = lean_mk_empty_array_with_capacity(v___x_5463_);
v___x_5465_ = lean_array_push(v___x_5464_, v_o_5431_);
v___x_5466_ = lean_array_push(v___x_5465_, v___x_5372_);
v___x_5467_ = lean_array_push(v___x_5466_, v_a_5461_);
v___x_5468_ = lean_array_push(v___x_5467_, v_e_5430_);
v___x_5469_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5458_, v___x_5462_, v___x_5468_, v_a_5356_);
lean_dec_ref(v___x_5468_);
return v___x_5469_;
}
else
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5477_; 
lean_dec_ref(v___x_5458_);
lean_dec_ref(v_o_5431_);
lean_dec_ref(v_e_5430_);
lean_dec_ref(v___x_5372_);
v_a_5470_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5472_ = v___x_5460_;
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5460_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5475_; 
if (v_isShared_5473_ == 0)
{
v___x_5475_ = v___x_5472_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5470_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
else
{
uint8_t v___x_5478_; 
v___x_5478_ = lean_nat_dec_eq(v_n_5432_, v_n_5454_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5479_ = lean_nat_sub(v_n_5454_, v_n_5432_);
lean_dec(v_n_5432_);
lean_dec(v_n_5454_);
v___x_5480_ = l_Lean_mkNatLit(v___x_5479_);
lean_inc_ref(v_e_5430_);
v___x_5481_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5430_, v___x_5480_);
v___y_5434_ = v___x_5481_;
goto v___jp_5433_;
}
else
{
lean_dec(v_n_5454_);
lean_dec(v_n_5432_);
lean_inc_ref(v_e_5430_);
v___y_5434_ = v_e_5430_;
goto v___jp_5433_;
}
}
}
else
{
lean_object* v_e_5482_; lean_object* v_o_5483_; lean_object* v_n_5484_; lean_object* v___y_5486_; uint8_t v___x_5508_; 
lean_dec_ref(v___x_5372_);
v_e_5482_ = lean_ctor_get(v_val_5429_, 0);
lean_inc_ref(v_e_5482_);
v_o_5483_ = lean_ctor_get(v_val_5429_, 1);
lean_inc_ref(v_o_5483_);
v_n_5484_ = lean_ctor_get(v_val_5429_, 2);
lean_inc(v_n_5484_);
lean_dec_ref_known(v_val_5429_, 3);
v___x_5508_ = lean_nat_dec_le(v_n_5432_, v_n_5484_);
if (v___x_5508_ == 0)
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5509_ = lean_nat_sub(v_n_5432_, v_n_5484_);
lean_dec(v_n_5484_);
lean_dec(v_n_5432_);
v___x_5510_ = l_Lean_mkNatLit(v___x_5509_);
lean_inc_ref(v_e_5430_);
v___x_5511_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5430_, v___x_5510_);
lean_inc_ref(v_e_5482_);
v___x_5512_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5511_, v_e_5482_);
lean_inc_ref(v_o_5431_);
lean_inc_ref(v_o_5483_);
v___x_5513_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5483_, v_o_5431_);
v___x_5514_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5513_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref_known(v___x_5514_, 1);
v___x_5516_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__9));
v___x_5517_ = lean_unsigned_to_nat(5u);
v___x_5518_ = lean_mk_empty_array_with_capacity(v___x_5517_);
v___x_5519_ = lean_array_push(v___x_5518_, v_e_5430_);
v___x_5520_ = lean_array_push(v___x_5519_, v_e_5482_);
v___x_5521_ = lean_array_push(v___x_5520_, v_o_5431_);
v___x_5522_ = lean_array_push(v___x_5521_, v_o_5483_);
v___x_5523_ = lean_array_push(v___x_5522_, v_a_5515_);
v___x_5524_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5512_, v___x_5516_, v___x_5523_, v_a_5356_);
lean_dec_ref(v___x_5523_);
return v___x_5524_;
}
else
{
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
lean_dec_ref(v___x_5512_);
lean_dec_ref(v_o_5483_);
lean_dec_ref(v_e_5482_);
lean_dec_ref(v_o_5431_);
lean_dec_ref(v_e_5430_);
v_a_5525_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___x_5514_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5514_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5525_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
}
else
{
uint8_t v___x_5533_; 
v___x_5533_ = lean_nat_dec_eq(v_n_5432_, v_n_5484_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
v___x_5534_ = lean_nat_sub(v_n_5484_, v_n_5432_);
lean_dec(v_n_5432_);
lean_dec(v_n_5484_);
v___x_5535_ = l_Lean_mkNatLit(v___x_5534_);
lean_inc_ref(v_e_5482_);
v___x_5536_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5482_, v___x_5535_);
v___y_5486_ = v___x_5536_;
goto v___jp_5485_;
}
else
{
lean_dec(v_n_5484_);
lean_dec(v_n_5432_);
lean_inc_ref(v_e_5482_);
v___y_5486_ = v_e_5482_;
goto v___jp_5485_;
}
}
v___jp_5485_:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; 
lean_inc_ref(v_e_5430_);
v___x_5487_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5430_, v___y_5486_);
lean_inc_ref(v_o_5483_);
lean_inc_ref(v_o_5431_);
v___x_5488_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5431_, v_o_5483_);
v___x_5489_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5488_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
lean_inc(v_a_5490_);
lean_dec_ref_known(v___x_5489_, 1);
v___x_5491_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__7));
v___x_5492_ = lean_unsigned_to_nat(5u);
v___x_5493_ = lean_mk_empty_array_with_capacity(v___x_5492_);
v___x_5494_ = lean_array_push(v___x_5493_, v_e_5430_);
v___x_5495_ = lean_array_push(v___x_5494_, v_e_5482_);
v___x_5496_ = lean_array_push(v___x_5495_, v_o_5431_);
v___x_5497_ = lean_array_push(v___x_5496_, v_o_5483_);
v___x_5498_ = lean_array_push(v___x_5497_, v_a_5490_);
v___x_5499_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5487_, v___x_5491_, v___x_5498_, v_a_5356_);
lean_dec_ref(v___x_5498_);
return v___x_5499_;
}
else
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5507_; 
lean_dec_ref(v___x_5487_);
lean_dec_ref(v_o_5483_);
lean_dec_ref(v_e_5482_);
lean_dec_ref(v_o_5431_);
lean_dec_ref(v_e_5430_);
v_a_5500_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5502_ = v___x_5489_;
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v___x_5489_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
}
v___jp_5433_:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
lean_inc_ref(v___x_5372_);
lean_inc_ref(v_o_5431_);
v___x_5435_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5431_, v___x_5372_);
v___x_5436_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5435_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5436_, 1);
v___x_5438_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__3));
v___x_5439_ = lean_unsigned_to_nat(4u);
v___x_5440_ = lean_mk_empty_array_with_capacity(v___x_5439_);
v___x_5441_ = lean_array_push(v___x_5440_, v_e_5430_);
v___x_5442_ = lean_array_push(v___x_5441_, v_o_5431_);
v___x_5443_ = lean_array_push(v___x_5442_, v___x_5372_);
v___x_5444_ = lean_array_push(v___x_5443_, v_a_5437_);
v___x_5445_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___y_5434_, v___x_5438_, v___x_5444_, v_a_5356_);
lean_dec_ref(v___x_5444_);
return v___x_5445_;
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec_ref(v___y_5434_);
lean_dec_ref(v_o_5431_);
lean_dec_ref(v_e_5430_);
lean_dec_ref(v___x_5372_);
v_a_5446_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___x_5436_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5436_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5451_; 
if (v_isShared_5449_ == 0)
{
v___x_5451_ = v___x_5448_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
}
}
else
{
lean_object* v___x_5537_; lean_object* v___x_5539_; 
lean_dec(v_a_5374_);
lean_dec_ref(v___x_5372_);
lean_dec(v_val_5371_);
lean_dec_ref(v_p_5364_);
v___x_5537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v___x_5537_);
v___x_5539_ = v___x_5376_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
lean_dec_ref(v___x_5372_);
lean_dec(v_val_5371_);
lean_dec_ref(v_p_5364_);
v_a_5542_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5544_ = v___x_5373_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5373_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
else
{
lean_object* v___x_5550_; lean_object* v___x_5552_; 
lean_dec(v_a_5367_);
lean_dec_ref(v_p_5364_);
v___x_5550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 0, v___x_5550_);
v___x_5552_ = v___x_5369_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec_ref(v_p_5364_);
v_a_5555_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5366_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5366_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object* v_e_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_){
_start:
{
lean_object* v_res_5569_; 
v_res_5569_ = l_Nat_reduceSubDiff___redArg(v_e_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec_ref(v_e_5563_);
return v_res_5569_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object* v_e_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_){
_start:
{
lean_object* v___x_5579_; 
v___x_5579_ = l_Nat_reduceSubDiff___redArg(v_e_5570_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_);
return v___x_5579_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object* v_e_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l_Nat_reduceSubDiff(v_e_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_);
lean_dec(v_a_5587_);
lean_dec_ref(v_a_5586_);
lean_dec(v_a_5585_);
lean_dec_ref(v_a_5584_);
lean_dec(v_a_5583_);
lean_dec_ref(v_a_5582_);
lean_dec(v_a_5581_);
lean_dec_ref(v_e_5580_);
return v_res_5589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v___x_5595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_));
v___x_5596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_5597_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5598_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5595_, v___x_5596_, v___x_5597_);
return v___x_5598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26____boxed(lean_object* v_a_5599_){
_start:
{
lean_object* v_res_5600_; 
v_res_5600_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_();
return v_res_5600_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; 
v___x_5601_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5602_, 0, v___x_5601_);
return v___x_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_5604_; uint8_t v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_));
v___x_5605_ = 1;
v___x_5606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_);
v___x_5607_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5604_, v___x_5605_, v___x_5606_);
return v___x_5607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28____boxed(lean_object* v_a_5608_){
_start:
{
lean_object* v_res_5609_; 
v_res_5609_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_();
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_5611_; uint8_t v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
v___x_5611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_));
v___x_5612_ = 1;
v___x_5613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_);
v___x_5614_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5611_, v___x_5612_, v___x_5613_);
return v___x_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_30____boxed(lean_object* v_a_5615_){
_start:
{
lean_object* v_res_5616_; 
v_res_5616_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_30_();
return v_res_5616_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5626_ = lean_box(0);
v___x_5627_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__4));
v___x_5628_ = l_Lean_mkConst(v___x_5627_, v___x_5626_);
return v___x_5628_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5633_ = lean_box(0);
v___x_5634_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__7));
v___x_5635_ = l_Lean_mkConst(v___x_5634_, v___x_5633_);
return v___x_5635_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5640_ = lean_box(0);
v___x_5641_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__10));
v___x_5642_ = l_Lean_mkConst(v___x_5641_, v___x_5640_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object* v_e_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v___x_5652_; 
v___x_5652_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5643_, v_a_5645_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5654_; uint8_t v___x_5655_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
lean_inc(v_a_5653_);
lean_dec_ref_known(v___x_5652_, 1);
v___x_5654_ = l_Lean_Expr_cleanupAnnotations(v_a_5653_);
v___x_5655_ = l_Lean_Expr_isApp(v___x_5654_);
if (v___x_5655_ == 0)
{
lean_dec_ref(v___x_5654_);
goto v___jp_5649_;
}
else
{
lean_object* v_arg_5656_; lean_object* v___x_5657_; uint8_t v___x_5658_; 
v_arg_5656_ = lean_ctor_get(v___x_5654_, 1);
lean_inc_ref(v_arg_5656_);
v___x_5657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5654_);
v___x_5658_ = l_Lean_Expr_isApp(v___x_5657_);
if (v___x_5658_ == 0)
{
lean_dec_ref(v___x_5657_);
lean_dec_ref(v_arg_5656_);
goto v___jp_5649_;
}
else
{
lean_object* v_arg_5659_; lean_object* v___x_5660_; uint8_t v___x_5661_; 
v_arg_5659_ = lean_ctor_get(v___x_5657_, 1);
lean_inc_ref(v_arg_5659_);
v___x_5660_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5657_);
v___x_5661_ = l_Lean_Expr_isApp(v___x_5660_);
if (v___x_5661_ == 0)
{
lean_dec_ref(v___x_5660_);
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
goto v___jp_5649_;
}
else
{
lean_object* v_arg_5662_; lean_object* v___x_5663_; uint8_t v___x_5664_; 
v_arg_5662_ = lean_ctor_get(v___x_5660_, 1);
lean_inc_ref(v_arg_5662_);
v___x_5663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5660_);
v___x_5664_ = l_Lean_Expr_isApp(v___x_5663_);
if (v___x_5664_ == 0)
{
lean_dec_ref(v___x_5663_);
lean_dec_ref(v_arg_5662_);
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
goto v___jp_5649_;
}
else
{
lean_object* v___x_5665_; lean_object* v___x_5666_; uint8_t v___x_5667_; 
v___x_5665_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5663_);
v___x_5666_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__2));
v___x_5667_ = l_Lean_Expr_isConstOf(v___x_5665_, v___x_5666_);
lean_dec_ref(v___x_5665_);
if (v___x_5667_ == 0)
{
lean_dec_ref(v_arg_5662_);
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
goto v___jp_5649_;
}
else
{
lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___x_5668_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__5, &l_Nat_reduceDvd___redArg___closed__5_once, _init_l_Nat_reduceDvd___redArg___closed__5);
v___x_5669_ = l_Lean_Meta_matchesInstance(v_arg_5662_, v___x_5668_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5756_; 
v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5672_ = v___x_5669_;
v_isShared_5673_ = v_isSharedCheck_5756_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v___x_5669_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5756_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
uint8_t v___x_5674_; 
v___x_5674_ = lean_unbox(v_a_5670_);
lean_dec(v_a_5670_);
if (v___x_5674_ == 0)
{
lean_object* v___x_5675_; lean_object* v___x_5677_; 
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
v___x_5675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5673_ == 0)
{
lean_ctor_set(v___x_5672_, 0, v___x_5675_);
v___x_5677_ = v___x_5672_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v___x_5675_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
else
{
lean_object* v___x_5679_; 
lean_del_object(v___x_5672_);
v___x_5679_ = l_Lean_Meta_getNatValue_x3f(v_arg_5659_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5747_; 
v_a_5680_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5747_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5682_ = v___x_5679_;
v_isShared_5683_ = v_isSharedCheck_5747_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5679_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5747_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
if (lean_obj_tag(v_a_5680_) == 1)
{
lean_object* v_val_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5742_; 
lean_del_object(v___x_5682_);
v_val_5684_ = lean_ctor_get(v_a_5680_, 0);
v_isSharedCheck_5742_ = !lean_is_exclusive(v_a_5680_);
if (v_isSharedCheck_5742_ == 0)
{
v___x_5686_ = v_a_5680_;
v_isShared_5687_ = v_isSharedCheck_5742_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_val_5684_);
lean_dec(v_a_5680_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5742_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5688_; 
v___x_5688_ = l_Lean_Meta_getNatValue_x3f(v_arg_5656_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5733_; 
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5733_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5733_ == 0)
{
v___x_5691_ = v___x_5688_;
v_isShared_5692_ = v_isSharedCheck_5733_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5688_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5733_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
if (lean_obj_tag(v_a_5689_) == 1)
{
lean_object* v_val_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5728_; 
v_val_5693_ = lean_ctor_get(v_a_5689_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v_a_5689_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5695_ = v_a_5689_;
v_isShared_5696_ = v_isSharedCheck_5728_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_val_5693_);
lean_dec(v_a_5689_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5728_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5697_; lean_object* v___x_5698_; uint8_t v___x_5699_; 
v___x_5697_ = lean_nat_mod(v_val_5693_, v_val_5684_);
lean_dec(v_val_5684_);
lean_dec(v_val_5693_);
v___x_5698_ = lean_unsigned_to_nat(0u);
v___x_5699_ = lean_nat_dec_eq(v___x_5697_, v___x_5698_);
lean_dec(v___x_5697_);
if (v___x_5699_ == 0)
{
lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5705_; 
v___x_5700_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_5701_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__8, &l_Nat_reduceDvd___redArg___closed__8_once, _init_l_Nat_reduceDvd___redArg___closed__8);
v___x_5702_ = l_Lean_eagerReflBoolTrue;
v___x_5703_ = l_Lean_mkApp3(v___x_5701_, v_arg_5659_, v_arg_5656_, v___x_5702_);
if (v_isShared_5696_ == 0)
{
lean_ctor_set(v___x_5695_, 0, v___x_5703_);
v___x_5705_ = v___x_5695_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5703_);
v___x_5705_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
lean_object* v___x_5706_; lean_object* v___x_5708_; 
v___x_5706_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5706_, 0, v___x_5700_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
lean_ctor_set_uint8(v___x_5706_, sizeof(void*)*2, v___x_5667_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set_tag(v___x_5686_, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5706_);
v___x_5708_ = v___x_5686_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v___x_5706_);
v___x_5708_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
lean_object* v___x_5710_; 
if (v_isShared_5692_ == 0)
{
lean_ctor_set(v___x_5691_, 0, v___x_5708_);
v___x_5710_ = v___x_5691_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5708_);
v___x_5710_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
return v___x_5710_;
}
}
}
}
else
{
lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5719_; 
v___x_5714_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_5715_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__11, &l_Nat_reduceDvd___redArg___closed__11_once, _init_l_Nat_reduceDvd___redArg___closed__11);
v___x_5716_ = l_Lean_eagerReflBoolTrue;
v___x_5717_ = l_Lean_mkApp3(v___x_5715_, v_arg_5659_, v_arg_5656_, v___x_5716_);
if (v_isShared_5696_ == 0)
{
lean_ctor_set(v___x_5695_, 0, v___x_5717_);
v___x_5719_ = v___x_5695_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5717_);
v___x_5719_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
lean_object* v___x_5720_; lean_object* v___x_5722_; 
v___x_5720_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5720_, 0, v___x_5714_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
lean_ctor_set_uint8(v___x_5720_, sizeof(void*)*2, v___x_5667_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set_tag(v___x_5686_, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5720_);
v___x_5722_ = v___x_5686_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v___x_5720_);
v___x_5722_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
lean_object* v___x_5724_; 
if (v_isShared_5692_ == 0)
{
lean_ctor_set(v___x_5691_, 0, v___x_5722_);
v___x_5724_ = v___x_5691_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v___x_5722_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
}
}
else
{
lean_object* v___x_5729_; lean_object* v___x_5731_; 
lean_dec(v_a_5689_);
lean_del_object(v___x_5686_);
lean_dec(v_val_5684_);
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
v___x_5729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5692_ == 0)
{
lean_ctor_set(v___x_5691_, 0, v___x_5729_);
v___x_5731_ = v___x_5691_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v___x_5729_);
v___x_5731_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
return v___x_5731_;
}
}
}
}
else
{
lean_object* v_a_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5741_; 
lean_del_object(v___x_5686_);
lean_dec(v_val_5684_);
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
v_a_5734_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5741_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5736_ = v___x_5688_;
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_a_5734_);
lean_dec(v___x_5688_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5739_; 
if (v_isShared_5737_ == 0)
{
v___x_5739_ = v___x_5736_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_a_5734_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
}
}
else
{
lean_object* v___x_5743_; lean_object* v___x_5745_; 
lean_dec(v_a_5680_);
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
v___x_5743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 0, v___x_5743_);
v___x_5745_ = v___x_5682_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5743_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
v_a_5748_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5679_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5679_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec_ref(v_arg_5659_);
lean_dec_ref(v_arg_5656_);
v_a_5757_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5669_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5669_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
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
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
v_a_5765_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5767_ = v___x_5652_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5652_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_a_5765_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
v___jp_5649_:
{
lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_5651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
return v___x_5651_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg___boxed(lean_object* v_e_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_){
_start:
{
lean_object* v_res_5779_; 
v_res_5779_ = l_Nat_reduceDvd___redArg(v_e_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
return v_res_5779_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object* v_e_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l_Nat_reduceDvd___redArg(v_e_5780_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object* v_e_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_Nat_reduceDvd(v_e_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_);
lean_dec(v_a_5797_);
lean_dec_ref(v_a_5796_);
lean_dec(v_a_5795_);
lean_dec_ref(v_a_5794_);
lean_dec(v_a_5793_);
lean_dec_ref(v_a_5792_);
lean_dec(v_a_5791_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5820_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5821_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5818_, v___x_5819_, v___x_5820_);
return v___x_5821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26____boxed(lean_object* v_a_5822_){
_start:
{
lean_object* v_res_5823_; 
v_res_5823_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_();
return v_res_5823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5825_, 0, v___x_5824_);
return v___x_5825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_5827_; uint8_t v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5828_ = 1;
v___x_5829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_);
v___x_5830_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5827_, v___x_5828_, v___x_5829_);
return v___x_5830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28____boxed(lean_object* v_a_5831_){
_start:
{
lean_object* v_res_5832_; 
v_res_5832_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_();
return v_res_5832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_5834_; uint8_t v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5835_ = 1;
v___x_5836_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_);
v___x_5837_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5834_, v___x_5835_, v___x_5836_);
return v___x_5837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30____boxed(lean_object* v_a_5838_){
_start:
{
lean_object* v_res_5839_; 
v_res_5839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30_();
return v_res_5839_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_PowMod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Nat_PowMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__24_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4165645285____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLog2_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLog2___regBuiltin_Nat_reduceLog2_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1090884023____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePowMod_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePowMod___regBuiltin_Nat_reducePowMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4157948570____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__114_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__119_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__201_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2511479442____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__206_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30_();
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
lean_object* initialize_Init_Data_Nat_PowMod(uint8_t builtin);
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
res = initialize_Init_Data_Nat_PowMod(builtin);
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
