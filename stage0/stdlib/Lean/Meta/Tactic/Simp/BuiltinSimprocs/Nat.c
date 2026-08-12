// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
// Imports: public import Init.Simproc public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util public import Lean.Meta.LitValues public import Lean.Meta.Offset import Lean.Util.SafeExponentiation import Init.Data.Nat.Dvd import Init.Data.Nat.Simproc import Lean.OrderLevel
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
extern lean_object* l_Lean_Nat_mkInstAdd;
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(209, 55, 73, 242, 185, 51, 64, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(167, 230, 249, 145, 254, 156, 61, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(171, 95, 24, 58, 17, 176, 174, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(231, 215, 207, 13, 249, 183, 176, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(183, 226, 154, 210, 11, 244, 146, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducePow"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(60, 231, 124, 151, 108, 38, 1, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reducePow___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(148, 61, 72, 84, 221, 248, 138, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceAnd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceXor"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(247, 188, 94, 215, 20, 109, 242, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceXor___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceOr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(221, 174, 173, 61, 215, 145, 106, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceOr___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(207, 233, 59, 9, 218, 201, 108, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(243, 57, 160, 187, 200, 59, 234, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceShiftRight___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceGcd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(82, 32, 179, 68, 111, 80, 212, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(226, 122, 83, 255, 56, 112, 58, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(188, 136, 66, 184, 194, 15, 6, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(103, 209, 103, 202, 56, 43, 177, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(177, 23, 93, 29, 19, 120, 61, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(190, 70, 159, 136, 109, 243, 67, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_isValue___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_eq_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 34, 5, 84, 182, 212, 65, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_add_gt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(236, 49, 75, 205, 14, 153, 197, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 221, 155, 114, 230, 4, 170, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_eq_gt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(222, 96, 15, 118, 250, 229, 166, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_eq_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(251, 19, 99, 115, 28, 102, 68, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_eq_add_ge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(145, 96, 71, 238, 158, 249, 159, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceEqDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(254, 236, 88, 131, 52, 249, 43, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBeqDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "beqFalseOfEqFalse"};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 37, 109, 252, 57, 80, 240, 250)}};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceBeqDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceBeqDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "beqEqOfEqEq"};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_1),((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 102, 212, 241, 77, 109, 37)}};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceBeqDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceBeqDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(241, 192, 105, 34, 163, 55, 67, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBneDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "bneTrueOfEqFalse"};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 18, 96, 112, 23, 126, 226, 206)}};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceBneDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceBneDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bneEqOfEqEq"};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value_aux_1),((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 158, 215, 107, 79, 237, 39, 137)}};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceBneDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceBneDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(187, 243, 98, 188, 219, 83, 246, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_le_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 38, 194, 84, 75, 182, 180, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_add_ge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 240, 107, 221, 21, 179, 249, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_add_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 232, 2, 112, 26, 243, 197, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_le_gt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(184, 68, 207, 87, 108, 168, 176, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_le_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 9, 215, 28, 195, 38, 233, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_le_add_ge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceLeDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(46, 217, 224, 205, 36, 202, 222, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "add_sub_add_le"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 51, 84, 134, 180, 46, 92, 43)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "add_sub_le"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__2 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__2_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 216, 225, 85, 93, 18, 232, 126)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "sub_add_eq_comm"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__4_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__5_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 127, 24, 115, 7, 168, 162, 198)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__5 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__5_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_sub_assoc"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__6 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__6_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value_aux_0),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(159, 186, 201, 236, 181, 193, 225, 53)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__7 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "add_sub_add_ge"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__8 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__8_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(48, 27, 181, 35, 241, 165, 108, 235)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__9 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceSubDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(56, 43, 140, 205, 20, 127, 167, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_30____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(113, 66, 62, 145, 3, 197, 80, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26____boxed(lean_object*);
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
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_756_, 1);
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
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_860_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_861_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_858_, v___x_859_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26____boxed(lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_();
return v_res_863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_868_ = 1;
v___x_869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_);
v___x_870_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_867_, v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28____boxed(lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_();
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
v___x_875_ = 1;
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_);
v___x_877_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_874_, v___x_875_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30____boxed(lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_();
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
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_899_, 1);
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
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_998_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_999_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_996_, v___x_997_, v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26____boxed(lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_();
return v_res_1001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_1006_ = 1;
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_);
v___x_1008_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1005_, v___x_1006_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28____boxed(lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_();
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_));
v___x_1013_ = 1;
v___x_1014_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_);
v___x_1015_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1012_, v___x_1013_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30____boxed(lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_();
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
v___x_1032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_1037_, 1);
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
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1136_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1137_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1134_, v___x_1135_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26____boxed(lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_();
return v_res_1139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1144_ = 1;
v___x_1145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_);
v___x_1146_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1143_, v___x_1144_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28____boxed(lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_();
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_1151_ = 1;
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_);
v___x_1153_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1150_, v___x_1151_, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30____boxed(lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_();
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
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_1175_, 1);
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
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1274_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1275_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1272_, v___x_1273_, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26____boxed(lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_();
return v_res_1277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1282_ = 1;
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_);
v___x_1284_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28____boxed(lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_();
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_));
v___x_1289_ = 1;
v___x_1290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_);
v___x_1291_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1288_, v___x_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30____boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_();
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
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_1313_, 1);
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
v___x_1337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1412_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1413_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1410_, v___x_1411_, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26____boxed(lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_();
return v_res_1415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1420_ = 1;
v___x_1421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_);
v___x_1422_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1419_, v___x_1420_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28____boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_();
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_));
v___x_1427_ = 1;
v___x_1428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_);
v___x_1429_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1426_, v___x_1427_, v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30____boxed(lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_();
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
lean_dec_ref_known(v_a_1465_, 1);
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
v___x_1487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1585_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1586_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1583_, v___x_1584_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26____boxed(lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_();
return v_res_1588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1593_ = 1;
v___x_1594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_);
v___x_1595_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1592_, v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28____boxed(lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_();
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_));
v___x_1600_ = 1;
v___x_1601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_);
v___x_1602_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1599_, v___x_1600_, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30____boxed(lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_();
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
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_1624_, 1);
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
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_1722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_1723_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_1724_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1721_, v___x_1722_, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26____boxed(lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_();
return v_res_1726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_1731_ = 1;
v___x_1732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_);
v___x_1733_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1730_, v___x_1731_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28____boxed(lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_();
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_));
v___x_1738_ = 1;
v___x_1739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_);
v___x_1740_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1737_, v___x_1738_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30____boxed(lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_();
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
v___x_1757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_1762_, 1);
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
v___x_1786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_1860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_1861_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_1862_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1859_, v___x_1860_, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26____boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_();
return v_res_1864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_1869_ = 1;
v___x_1870_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_);
v___x_1871_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1868_, v___x_1869_, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28____boxed(lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_();
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_));
v___x_1876_ = 1;
v___x_1877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_);
v___x_1878_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1875_, v___x_1876_, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30____boxed(lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_();
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
v___x_1895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_1900_, 1);
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
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_1937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_1999_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2000_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1997_, v___x_1998_, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26____boxed(lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_();
return v_res_2002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_2007_ = 1;
v___x_2008_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_);
v___x_2009_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2006_, v___x_2007_, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28____boxed(lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_));
v___x_2014_ = 1;
v___x_2015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_);
v___x_2016_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2013_, v___x_2014_, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30____boxed(lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_();
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
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_2038_, 1);
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
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2137_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2138_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2135_, v___x_2136_, v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26____boxed(lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_();
return v_res_2140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2145_ = 1;
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_);
v___x_2147_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2144_, v___x_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28____boxed(lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_();
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_));
v___x_2152_ = 1;
v___x_2153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_);
v___x_2154_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2151_, v___x_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30____boxed(lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_();
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
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_2176_, 1);
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
v___x_2200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_2213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2275_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2276_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2273_, v___x_2274_, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26____boxed(lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_();
return v_res_2278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2283_ = 1;
v___x_2284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_);
v___x_2285_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2282_, v___x_2283_, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28____boxed(lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_();
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_));
v___x_2290_ = 1;
v___x_2291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_);
v___x_2292_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2289_, v___x_2290_, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30____boxed(lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_();
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
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_2313_, 1);
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
v___x_2337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_2350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2407_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2408_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2405_, v___x_2406_, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21____boxed(lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_();
return v_res_2410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2415_ = 1;
v___x_2416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_);
v___x_2417_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2414_, v___x_2415_, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23____boxed(lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_();
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_));
v___x_2422_ = 1;
v___x_2423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_);
v___x_2424_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2421_, v___x_2422_, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25____boxed(lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_();
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
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
lean_dec_ref_known(v_a_2446_, 1);
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
lean_dec_ref_known(v_a_2453_, 1);
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
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2533_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2534_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2531_, v___x_2532_, v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27____boxed(lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_();
return v_res_2536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2541_ = 1;
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_);
v___x_2543_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2540_, v___x_2541_, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29____boxed(lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_();
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2548_ = 1;
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_);
v___x_2550_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2547_, v___x_2548_, v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31____boxed(lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_();
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
v___x_2567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
lean_dec_ref_known(v_a_2572_, 1);
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
lean_dec_ref_known(v_a_2579_, 1);
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
v___x_2586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_));
v___x_2645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_));
v___x_2646_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2647_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2644_, v___x_2645_, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27____boxed(lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_();
return v_res_2649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_));
v___x_2654_ = 1;
v___x_2655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_);
v___x_2656_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2653_, v___x_2654_, v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29____boxed(lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_();
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_));
v___x_2661_ = 1;
v___x_2662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_);
v___x_2663_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2660_, v___x_2661_, v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31____boxed(lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_();
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
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_2695_, 1);
v___x_2708_ = lean_nat_dec_eq(v_val_2689_, v_val_2707_);
lean_dec(v_val_2707_);
lean_dec(v_val_2689_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_2700_ = v___x_2709_;
goto v___jp_2699_;
}
else
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
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
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_2725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_2785_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_2786_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2783_, v___x_2784_, v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27____boxed(lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_();
return v_res_2788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_2793_ = 1;
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_);
v___x_2795_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2792_, v___x_2793_, v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29____boxed(lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_();
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_2800_ = 1;
v___x_2801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_);
v___x_2802_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2799_, v___x_2800_, v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31____boxed(lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_();
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
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_2832_, 1);
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
v___x_2848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
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
v___x_2849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
v___x_2845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
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
v___x_2863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_2922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_2923_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_2924_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2921_, v___x_2922_, v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27____boxed(lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_();
return v_res_2926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_2931_ = 1;
v___x_2932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_);
v___x_2933_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2930_, v___x_2931_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29____boxed(lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_();
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_2938_ = 1;
v___x_2939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_);
v___x_2940_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2937_, v___x_2938_, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31____boxed(lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_();
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
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_));
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_));
v___x_3024_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3025_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3022_, v___x_3023_, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23____boxed(lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_();
return v_res_3027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_));
v___x_3032_ = 1;
v___x_3033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_);
v___x_3034_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3031_, v___x_3032_, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25____boxed(lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_();
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
lean_dec_ref_known(v_t_3042_, 1);
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
lean_dec_ref_known(v_t_3042_, 3);
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
lean_dec_ref_known(v___x_3288_, 1);
lean_dec_ref(v_e_3287_);
v_val_3302_ = lean_ctor_get(v_a_3289_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v_a_3289_, 1);
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
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_));
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3603_ = lean_box(0);
v___x_3604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4));
v___x_3605_ = l_Lean_mkConst(v___x_3604_, v___x_3603_);
return v___x_3605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5);
v___x_3607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3608_ = lean_array_push(v___x_3607_, v___x_3606_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object* v_u_3609_, lean_object* v_x_3610_, lean_object* v_y_3611_){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_3613_ = lean_box(0);
v___x_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_u_3609_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_Expr_const___override(v___x_3612_, v___x_3614_);
v___x_3616_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6);
v___x_3617_ = lean_array_push(v___x_3616_, v_x_3610_);
v___x_3618_ = lean_array_push(v___x_3617_, v_y_3611_);
v___x_3619_ = l_Lean_mkAppN(v___x_3615_, v___x_3618_);
lean_dec_ref(v___x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object* v_u_3620_, lean_object* v_x_3621_, lean_object* v_y_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_u_3620_, v_y_3622_, v_x_3621_);
return v___x_3623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2(void){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3627_ = lean_box(0);
v___x_3628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1));
v___x_3629_ = l_Lean_mkConst(v___x_3628_, v___x_3627_);
return v___x_3629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2);
v___x_3631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3632_ = lean_array_push(v___x_3631_, v___x_3630_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object* v_u_3633_, lean_object* v_x_3634_, lean_object* v_y_3635_){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3636_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_3637_ = lean_box(0);
v___x_3638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_u_3633_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = l_Lean_Expr_const___override(v___x_3636_, v___x_3638_);
v___x_3640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3);
v___x_3641_ = lean_array_push(v___x_3640_, v_x_3634_);
v___x_3642_ = lean_array_push(v___x_3641_, v_y_3635_);
v___x_3643_ = l_Lean_mkAppN(v___x_3639_, v___x_3642_);
lean_dec_ref(v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object* v_u_3644_, lean_object* v_x_3645_, lean_object* v_y_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_u_3644_, v_y_3646_, v_x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_box(0);
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1));
v___x_3653_ = l_Lean_mkConst(v___x_3652_, v___x_3651_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object* v_p_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3660_; 
lean_inc_ref(v_p_3654_);
v___x_3660_ = l_Lean_Meta_mkDecide(v_p_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v___x_3662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___x_3663_ = l_Lean_Meta_mkEqRefl(v___x_3662_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3679_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3679_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3679_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2);
v___x_3669_ = l_Lean_Expr_appArg_x21(v_a_3661_);
lean_dec(v_a_3661_);
v___x_3670_ = lean_unsigned_to_nat(3u);
v___x_3671_ = lean_mk_empty_array_with_capacity(v___x_3670_);
v___x_3672_ = lean_array_push(v___x_3671_, v_p_3654_);
v___x_3673_ = lean_array_push(v___x_3672_, v___x_3669_);
v___x_3674_ = lean_array_push(v___x_3673_, v_a_3664_);
v___x_3675_ = l_Lean_mkAppN(v___x_3668_, v___x_3674_);
lean_dec_ref(v___x_3674_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3675_);
v___x_3677_ = v___x_3666_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
lean_dec(v_a_3661_);
lean_dec_ref(v_p_3654_);
return v___x_3663_;
}
}
else
{
lean_dec_ref(v_p_3654_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___boxed(lean_object* v_p_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v_p_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(lean_object* v_expr_3687_, lean_object* v_nm_3688_, lean_object* v_args_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v___x_3692_; lean_object* v_env_3693_; uint8_t v___x_3694_; uint8_t v___x_3695_; 
v___x_3692_ = lean_st_ref_get(v_a_3690_);
v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_ref(v_env_3693_);
lean_dec(v___x_3692_);
v___x_3694_ = 1;
lean_inc(v_nm_3688_);
v___x_3695_ = l_Lean_Environment_contains(v_env_3693_, v_nm_3688_, v___x_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec(v_nm_3688_);
lean_dec_ref(v_expr_3687_);
v___x_3696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
return v___x_3697_;
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3698_ = lean_box(0);
v___x_3699_ = l_Lean_mkConst(v_nm_3688_, v___x_3698_);
v___x_3700_ = l_Lean_mkAppN(v___x_3699_, v_args_3689_);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3702_, 0, v_expr_3687_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
lean_ctor_set_uint8(v___x_3702_, sizeof(void*)*2, v___x_3694_);
v___x_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
return v___x_3704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg___boxed(lean_object* v_expr_3705_, lean_object* v_nm_3706_, lean_object* v_args_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v_expr_3705_, v_nm_3706_, v_args_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_args_3707_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst(lean_object* v_expr_3711_, lean_object* v_nm_3712_, lean_object* v_args_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v_expr_3711_, v_nm_3712_, v_args_3713_, v_a_3720_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___boxed(lean_object* v_expr_3723_, lean_object* v_nm_3724_, lean_object* v_args_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst(v_expr_3723_, v_nm_3724_, v_args_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_args_3725_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx(lean_object* v_x_3735_){
_start:
{
switch(lean_obj_tag(v_x_3735_))
{
case 0:
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_unsigned_to_nat(0u);
return v___x_3736_;
}
case 1:
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_unsigned_to_nat(1u);
return v___x_3737_;
}
default: 
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_unsigned_to_nat(2u);
return v___x_3738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx___boxed(lean_object* v_x_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorIdx(v_x_3739_);
lean_dec_ref(v_x_3739_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(lean_object* v_t_3741_, lean_object* v_k_3742_){
_start:
{
switch(lean_obj_tag(v_t_3741_))
{
case 0:
{
uint8_t v_b_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_b_3743_ = lean_ctor_get_uint8(v_t_3741_, 0);
lean_dec_ref_known(v_t_3741_, 0);
v___x_3744_ = lean_box(v_b_3743_);
v___x_3745_ = lean_apply_1(v_k_3742_, v___x_3744_);
return v___x_3745_;
}
case 1:
{
lean_object* v_p_3746_; lean_object* v___x_3747_; 
v_p_3746_ = lean_ctor_get(v_t_3741_, 0);
lean_inc_ref(v_p_3746_);
lean_dec_ref_known(v_t_3741_, 1);
v___x_3747_ = lean_apply_1(v_k_3742_, v_p_3746_);
return v___x_3747_;
}
default: 
{
lean_object* v_x_3748_; lean_object* v_y_3749_; lean_object* v_p_3750_; lean_object* v___x_3751_; 
v_x_3748_ = lean_ctor_get(v_t_3741_, 0);
lean_inc_ref(v_x_3748_);
v_y_3749_ = lean_ctor_get(v_t_3741_, 1);
lean_inc_ref(v_y_3749_);
v_p_3750_ = lean_ctor_get(v_t_3741_, 2);
lean_inc_ref(v_p_3750_);
lean_dec_ref_known(v_t_3741_, 3);
v___x_3751_ = lean_apply_3(v_k_3742_, v_x_3748_, v_y_3749_, v_p_3750_);
return v___x_3751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim(lean_object* v_motive_3752_, lean_object* v_ctorIdx_3753_, lean_object* v_t_3754_, lean_object* v_h_3755_, lean_object* v_k_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3754_, v_k_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___boxed(lean_object* v_motive_3758_, lean_object* v_ctorIdx_3759_, lean_object* v_t_3760_, lean_object* v_h_3761_, lean_object* v_k_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim(v_motive_3758_, v_ctorIdx_3759_, v_t_3760_, v_h_3761_, v_k_3762_);
lean_dec(v_ctorIdx_3759_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_decide_elim___redArg(lean_object* v_t_3764_, lean_object* v_decide_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3764_, v_decide_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_decide_elim(lean_object* v_motive_3767_, lean_object* v_t_3768_, lean_object* v_h_3769_, lean_object* v_decide_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3768_, v_decide_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_false_elim___redArg(lean_object* v_t_3772_, lean_object* v_false_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3772_, v_false_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_false_elim(lean_object* v_motive_3775_, lean_object* v_t_3776_, lean_object* v_h_3777_, lean_object* v_false_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3776_, v_false_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_eq_elim___redArg(lean_object* v_t_3780_, lean_object* v_eq_3781_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3780_, v_eq_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_eq_elim(lean_object* v_motive_3783_, lean_object* v_t_3784_, lean_object* v_h_3785_, lean_object* v_eq_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_EqResult_ctorElim___redArg(v_t_3784_, v_eq_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(lean_object* v_e_3788_, lean_object* v_lemmaName_3789_, lean_object* v_args_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v___x_3793_; lean_object* v_env_3794_; uint8_t v___x_3795_; uint8_t v___x_3796_; 
v___x_3793_ = lean_st_ref_get(v_a_3791_);
v_env_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc_ref(v_env_3794_);
lean_dec(v___x_3793_);
v___x_3795_ = 1;
lean_inc(v_lemmaName_3789_);
v___x_3796_ = l_Lean_Environment_contains(v_env_3794_, v_lemmaName_3789_, v___x_3795_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec(v_lemmaName_3789_);
lean_dec_ref(v_e_3788_);
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
return v___x_3798_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3799_ = lean_box(0);
v___x_3800_ = l_Lean_mkConst(v_lemmaName_3789_, v___x_3799_);
v___x_3801_ = l_Lean_mkAppN(v___x_3800_, v_args_3790_);
v___x_3802_ = lean_apply_1(v_e_3788_, v___x_3801_);
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg___boxed(lean_object* v_e_3805_, lean_object* v_lemmaName_3806_, lean_object* v_args_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v_e_3805_, v_lemmaName_3806_, v_args_3807_, v_a_3808_);
lean_dec(v_a_3808_);
lean_dec_ref(v_args_3807_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma(lean_object* v_e_3811_, lean_object* v_lemmaName_3812_, lean_object* v_args_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v_e_3811_, v_lemmaName_3812_, v_args_3813_, v_a_3820_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___boxed(lean_object* v_e_3823_, lean_object* v_lemmaName_3824_, lean_object* v_args_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma(v_e_3823_, v_lemmaName_3824_, v_args_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_a_3830_);
lean_dec_ref(v_a_3829_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_args_3825_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__0(lean_object* v_p_3835_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_p_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2(lean_object* v_n_3837_, lean_object* v_n_3838_, lean_object* v_e_3839_, lean_object* v_p_3840_){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = lean_nat_sub(v_n_3837_, v_n_3838_);
v___x_3842_ = l_Lean_mkNatLit(v___x_3841_);
v___x_3843_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3843_, 0, v_e_3839_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
lean_ctor_set(v___x_3843_, 2, v_p_3840_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed(lean_object* v_n_3844_, lean_object* v_n_3845_, lean_object* v_e_3846_, lean_object* v_p_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2(v_n_3844_, v_n_3845_, v_e_3846_, v_p_3847_);
lean_dec(v_n_3845_);
lean_dec(v_n_3844_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__3(lean_object* v___x_3849_, lean_object* v_e_3850_, lean_object* v_p_3851_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v_e_3850_);
lean_ctor_set(v___x_3852_, 2, v_p_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__1(lean_object* v_e_3853_, lean_object* v___y_3854_, lean_object* v_p_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3856_, 0, v_e_3853_);
lean_ctor_set(v___x_3856_, 1, v___y_3854_);
lean_ctor_set(v___x_3856_, 2, v_p_3855_);
return v___x_3856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_unsigned_to_nat(0u);
v___x_3890_ = l_Lean_Level_ofNat(v___x_3889_);
return v___x_3890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = l_Lean_Level_ofNat(v___x_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(lean_object* v_x_3893_, lean_object* v_y_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_x_3893_);
v___x_3934_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_3893_, v___x_3933_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_4124_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_4124_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_4124_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
if (lean_obj_tag(v_a_3935_) == 1)
{
lean_object* v_val_3939_; lean_object* v___x_3940_; 
lean_del_object(v___x_3937_);
v_val_3939_ = lean_ctor_get(v_a_3935_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v_a_3935_, 1);
lean_inc_ref(v_y_3894_);
v___x_3940_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_3894_, v___x_3933_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_4111_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_3943_ = v___x_3940_;
v_isShared_3944_ = v_isSharedCheck_4111_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3940_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_4111_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
if (lean_obj_tag(v_a_3941_) == 1)
{
lean_object* v_val_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_4106_; 
lean_del_object(v___x_3943_);
v_val_3945_ = lean_ctor_get(v_a_3941_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_a_3941_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_3947_ = v_a_3941_;
v_isShared_3948_ = v_isSharedCheck_4106_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_val_3945_);
lean_dec(v_a_3941_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_4106_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_leCarrierIsSort(v_a_3897_, v_a_3898_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_4097_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_3952_ = v___x_3949_;
v_isShared_3953_ = v_isSharedCheck_4097_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_4097_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___f_3954_; lean_object* v_leLvl_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; uint8_t v___x_4094_; 
v___f_3954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__3));
v___x_4094_ = lean_unbox(v_a_3950_);
lean_dec(v_a_3950_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14);
v_leLvl_3956_ = v___x_4095_;
v___y_3957_ = v_a_3895_;
v___y_3958_ = v_a_3896_;
v___y_3959_ = v_a_3897_;
v___y_3960_ = v_a_3898_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15);
v_leLvl_3956_ = v___x_4096_;
v___y_3957_ = v_a_3895_;
v___y_3958_ = v_a_3896_;
v___y_3959_ = v_a_3897_;
v___y_3960_ = v_a_3898_;
goto v___jp_3955_;
}
v___jp_3955_:
{
if (lean_obj_tag(v_val_3939_) == 0)
{
lean_dec_ref(v_y_3894_);
if (lean_obj_tag(v_val_3945_) == 0)
{
lean_object* v_n_3961_; lean_object* v_n_3962_; uint8_t v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
lean_dec_ref(v_x_3893_);
v_n_3961_ = lean_ctor_get(v_val_3939_, 0);
lean_inc(v_n_3961_);
lean_dec_ref_known(v_val_3939_, 1);
v_n_3962_ = lean_ctor_get(v_val_3945_, 0);
lean_inc(v_n_3962_);
lean_dec_ref_known(v_val_3945_, 1);
v___x_3963_ = lean_nat_dec_eq(v_n_3961_, v_n_3962_);
lean_dec(v_n_3962_);
lean_dec(v_n_3961_);
v___x_3964_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3964_, 0, v___x_3963_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3964_);
v___x_3966_ = v___x_3947_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3968_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3966_);
v___x_3968_ = v___x_3952_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
else
{
lean_object* v_n_3971_; lean_object* v_e_3972_; lean_object* v_o_3973_; lean_object* v_n_3974_; uint8_t v___x_3975_; 
lean_del_object(v___x_3952_);
lean_del_object(v___x_3947_);
v_n_3971_ = lean_ctor_get(v_val_3939_, 0);
lean_inc(v_n_3971_);
lean_dec_ref_known(v_val_3939_, 1);
v_e_3972_ = lean_ctor_get(v_val_3945_, 0);
lean_inc_ref(v_e_3972_);
v_o_3973_ = lean_ctor_get(v_val_3945_, 1);
lean_inc_ref(v_o_3973_);
v_n_3974_ = lean_ctor_get(v_val_3945_, 2);
lean_inc(v_n_3974_);
lean_dec_ref_known(v_val_3945_, 3);
v___x_3975_ = lean_nat_dec_le(v_n_3974_, v_n_3971_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec(v_n_3974_);
lean_dec(v_n_3971_);
lean_inc_ref(v_o_3973_);
lean_inc_ref(v_x_3893_);
lean_inc(v_leLvl_3956_);
v___x_3976_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_leLvl_3956_, v_x_3893_, v_o_3973_);
v___x_3977_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3976_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v___x_3977_, 1);
v___x_3979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__5));
v___x_3980_ = lean_unsigned_to_nat(4u);
v___x_3981_ = lean_mk_empty_array_with_capacity(v___x_3980_);
v___x_3982_ = lean_array_push(v___x_3981_, v_x_3893_);
v___x_3983_ = lean_array_push(v___x_3982_, v_e_3972_);
v___x_3984_ = lean_array_push(v___x_3983_, v_o_3973_);
v___x_3985_ = lean_array_push(v___x_3984_, v_a_3978_);
v___x_3986_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_3954_, v___x_3979_, v___x_3985_, v___y_3960_);
lean_dec_ref(v___x_3985_);
return v___x_3986_;
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec_ref(v_o_3973_);
lean_dec_ref(v_e_3972_);
lean_dec_ref(v_x_3893_);
v_a_3987_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3977_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3977_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_inc_ref(v_x_3893_);
lean_inc_ref(v_o_3973_);
lean_inc(v_leLvl_3956_);
v___x_3995_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_3956_, v_o_3973_, v_x_3893_);
v___x_3996_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3995_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___f_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
lean_inc_ref(v_e_3972_);
v___f_3998_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3998_, 0, v_n_3971_);
lean_closure_set(v___f_3998_, 1, v_n_3974_);
lean_closure_set(v___f_3998_, 2, v_e_3972_);
v___x_3999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__7));
v___x_4000_ = lean_unsigned_to_nat(4u);
v___x_4001_ = lean_mk_empty_array_with_capacity(v___x_4000_);
v___x_4002_ = lean_array_push(v___x_4001_, v_x_3893_);
v___x_4003_ = lean_array_push(v___x_4002_, v_e_3972_);
v___x_4004_ = lean_array_push(v___x_4003_, v_o_3973_);
v___x_4005_ = lean_array_push(v___x_4004_, v_a_3997_);
v___x_4006_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_3998_, v___x_3999_, v___x_4005_, v___y_3960_);
lean_dec_ref(v___x_4005_);
return v___x_4006_;
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v_n_3974_);
lean_dec_ref(v_o_3973_);
lean_dec_ref(v_e_3972_);
lean_dec(v_n_3971_);
lean_dec_ref(v_x_3893_);
v_a_4007_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3996_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3996_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3952_);
lean_del_object(v___x_3947_);
lean_dec_ref(v_x_3893_);
if (lean_obj_tag(v_val_3945_) == 0)
{
lean_object* v_e_4015_; lean_object* v_o_4016_; lean_object* v_n_4017_; lean_object* v_n_4018_; uint8_t v___x_4019_; 
v_e_4015_ = lean_ctor_get(v_val_3939_, 0);
lean_inc_ref(v_e_4015_);
v_o_4016_ = lean_ctor_get(v_val_3939_, 1);
lean_inc_ref(v_o_4016_);
v_n_4017_ = lean_ctor_get(v_val_3939_, 2);
lean_inc(v_n_4017_);
lean_dec_ref_known(v_val_3939_, 3);
v_n_4018_ = lean_ctor_get(v_val_3945_, 0);
lean_inc(v_n_4018_);
lean_dec_ref_known(v_val_3945_, 1);
v___x_4019_ = lean_nat_dec_le(v_n_4017_, v_n_4018_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec(v_n_4018_);
lean_dec(v_n_4017_);
lean_inc_ref(v_o_4016_);
lean_inc_ref(v_y_3894_);
lean_inc(v_leLvl_3956_);
v___x_4020_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_leLvl_3956_, v_y_3894_, v_o_4016_);
v___x_4021_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4020_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__9));
v___x_4024_ = lean_unsigned_to_nat(4u);
v___x_4025_ = lean_mk_empty_array_with_capacity(v___x_4024_);
v___x_4026_ = lean_array_push(v___x_4025_, v_e_4015_);
v___x_4027_ = lean_array_push(v___x_4026_, v_o_4016_);
v___x_4028_ = lean_array_push(v___x_4027_, v_y_3894_);
v___x_4029_ = lean_array_push(v___x_4028_, v_a_4022_);
v___x_4030_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_3954_, v___x_4023_, v___x_4029_, v___y_3960_);
lean_dec_ref(v___x_4029_);
return v___x_4030_;
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec_ref(v_o_4016_);
lean_dec_ref(v_e_4015_);
lean_dec_ref(v_y_3894_);
v_a_4031_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4021_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4021_);
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
else
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_inc_ref(v_y_3894_);
lean_inc_ref(v_o_4016_);
lean_inc(v_leLvl_3956_);
v___x_4039_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_3956_, v_o_4016_, v_y_3894_);
v___x_4040_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4039_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___f_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
lean_inc_ref(v_e_4015_);
v___f_4042_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4042_, 0, v_n_4018_);
lean_closure_set(v___f_4042_, 1, v_n_4017_);
lean_closure_set(v___f_4042_, 2, v_e_4015_);
v___x_4043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__11));
v___x_4044_ = lean_unsigned_to_nat(4u);
v___x_4045_ = lean_mk_empty_array_with_capacity(v___x_4044_);
v___x_4046_ = lean_array_push(v___x_4045_, v_e_4015_);
v___x_4047_ = lean_array_push(v___x_4046_, v_o_4016_);
v___x_4048_ = lean_array_push(v___x_4047_, v_y_3894_);
v___x_4049_ = lean_array_push(v___x_4048_, v_a_4041_);
v___x_4050_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4042_, v___x_4043_, v___x_4049_, v___y_3960_);
lean_dec_ref(v___x_4049_);
return v___x_4050_;
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_n_4018_);
lean_dec(v_n_4017_);
lean_dec_ref(v_o_4016_);
lean_dec_ref(v_e_4015_);
lean_dec_ref(v_y_3894_);
v_a_4051_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4040_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4040_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
else
{
lean_object* v_e_4059_; lean_object* v_o_4060_; lean_object* v_n_4061_; lean_object* v_e_4062_; lean_object* v_o_4063_; lean_object* v_n_4064_; uint8_t v___x_4065_; 
lean_dec_ref(v_y_3894_);
v_e_4059_ = lean_ctor_get(v_val_3939_, 0);
lean_inc_ref(v_e_4059_);
v_o_4060_ = lean_ctor_get(v_val_3939_, 1);
lean_inc_ref(v_o_4060_);
v_n_4061_ = lean_ctor_get(v_val_3939_, 2);
lean_inc(v_n_4061_);
lean_dec_ref_known(v_val_3939_, 3);
v_e_4062_ = lean_ctor_get(v_val_3945_, 0);
lean_inc_ref(v_e_4062_);
v_o_4063_ = lean_ctor_get(v_val_3945_, 1);
lean_inc_ref(v_o_4063_);
v_n_4064_ = lean_ctor_get(v_val_3945_, 2);
lean_inc(v_n_4064_);
lean_dec_ref_known(v_val_3945_, 3);
v___x_4065_ = lean_nat_dec_le(v_n_4061_, v_n_4064_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
lean_inc_ref(v_o_4060_);
lean_inc_ref(v_o_4063_);
lean_inc(v_leLvl_3956_);
v___x_4066_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_3956_, v_o_4063_, v_o_4060_);
v___x_4067_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4066_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___f_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = lean_nat_sub(v_n_4061_, v_n_4064_);
lean_dec(v_n_4064_);
lean_dec(v_n_4061_);
v___x_4070_ = l_Lean_mkNatLit(v___x_4069_);
lean_inc_ref(v_e_4059_);
v___x_4071_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4059_, v___x_4070_);
lean_inc_ref(v_e_4062_);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__3), 3, 2);
lean_closure_set(v___f_4072_, 0, v___x_4071_);
lean_closure_set(v___f_4072_, 1, v_e_4062_);
v___x_4073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__13));
v___x_4074_ = lean_unsigned_to_nat(5u);
v___x_4075_ = lean_mk_empty_array_with_capacity(v___x_4074_);
v___x_4076_ = lean_array_push(v___x_4075_, v_e_4059_);
v___x_4077_ = lean_array_push(v___x_4076_, v_e_4062_);
v___x_4078_ = lean_array_push(v___x_4077_, v_o_4060_);
v___x_4079_ = lean_array_push(v___x_4078_, v_o_4063_);
v___x_4080_ = lean_array_push(v___x_4079_, v_a_4068_);
v___x_4081_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_4072_, v___x_4073_, v___x_4080_, v___y_3960_);
lean_dec_ref(v___x_4080_);
return v___x_4081_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_n_4064_);
lean_dec_ref(v_o_4063_);
lean_dec_ref(v_e_4062_);
lean_dec(v_n_4061_);
lean_dec_ref(v_o_4060_);
lean_dec_ref(v_e_4059_);
v_a_4082_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4067_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4067_);
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
uint8_t v___x_4090_; 
v___x_4090_ = lean_nat_dec_eq(v_n_4061_, v_n_4064_);
if (v___x_4090_ == 0)
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = lean_nat_sub(v_n_4064_, v_n_4061_);
lean_dec(v_n_4061_);
lean_dec(v_n_4064_);
v___x_4092_ = l_Lean_mkNatLit(v___x_4091_);
lean_inc_ref(v_e_4062_);
v___x_4093_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4062_, v___x_4092_);
lean_inc_ref(v_e_4059_);
v___y_3901_ = v_e_4059_;
v___y_3902_ = v___y_3958_;
v___y_3903_ = v_e_4059_;
v___y_3904_ = v_e_4062_;
v___y_3905_ = v___y_3959_;
v___y_3906_ = v_o_4063_;
v___y_3907_ = v___y_3957_;
v___y_3908_ = v___y_3960_;
v___y_3909_ = v_o_4060_;
v___y_3910_ = v_leLvl_3956_;
v___y_3911_ = v___x_4093_;
goto v___jp_3900_;
}
else
{
lean_dec(v_n_4064_);
lean_dec(v_n_4061_);
lean_inc_ref(v_e_4062_);
lean_inc_ref(v_e_4059_);
v___y_3901_ = v_e_4059_;
v___y_3902_ = v___y_3958_;
v___y_3903_ = v_e_4059_;
v___y_3904_ = v_e_4062_;
v___y_3905_ = v___y_3959_;
v___y_3906_ = v_o_4063_;
v___y_3907_ = v___y_3957_;
v___y_3908_ = v___y_3960_;
v___y_3909_ = v_o_4060_;
v___y_3910_ = v_leLvl_3956_;
v___y_3911_ = v_e_4062_;
goto v___jp_3900_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_del_object(v___x_3947_);
lean_dec(v_val_3945_);
lean_dec(v_val_3939_);
lean_dec_ref(v_y_3894_);
lean_dec_ref(v_x_3893_);
v_a_4098_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_3949_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_3949_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4109_; 
lean_dec(v_a_3941_);
lean_dec(v_val_3939_);
lean_dec_ref(v_y_3894_);
lean_dec_ref(v_x_3893_);
v___x_4107_ = lean_box(0);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v___x_4107_);
v___x_4109_ = v___x_3943_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v_val_3939_);
lean_dec_ref(v_y_3894_);
lean_dec_ref(v_x_3893_);
v_a_4112_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_3940_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_3940_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
else
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
lean_dec(v_a_3935_);
lean_dec_ref(v_y_3894_);
lean_dec_ref(v_x_3893_);
v___x_4120_ = lean_box(0);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_4120_);
v___x_4122_ = v___x_3937_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref(v_y_3894_);
lean_dec_ref(v_x_3893_);
v_a_4125_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_3934_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_3934_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
v___jp_3900_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_inc_ref(v___y_3906_);
lean_inc_ref(v___y_3909_);
lean_inc(v___y_3910_);
v___x_3912_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_3910_, v___y_3909_, v___y_3906_);
v___x_3913_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3912_, v___y_3907_, v___y_3902_, v___y_3905_, v___y_3908_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___f_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___f_3915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3915_, 0, v___y_3901_);
lean_closure_set(v___f_3915_, 1, v___y_3911_);
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__2));
v___x_3917_ = lean_unsigned_to_nat(5u);
v___x_3918_ = lean_mk_empty_array_with_capacity(v___x_3917_);
v___x_3919_ = lean_array_push(v___x_3918_, v___y_3903_);
v___x_3920_ = lean_array_push(v___x_3919_, v___y_3904_);
v___x_3921_ = lean_array_push(v___x_3920_, v___y_3909_);
v___x_3922_ = lean_array_push(v___x_3921_, v___y_3906_);
v___x_3923_ = lean_array_push(v___x_3922_, v_a_3914_);
v___x_3924_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applyEqLemma___redArg(v___f_3915_, v___x_3916_, v___x_3923_, v___y_3908_);
lean_dec_ref(v___x_3923_);
return v___x_3924_;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v___y_3911_);
lean_dec_ref(v___y_3909_);
lean_dec_ref(v___y_3906_);
lean_dec_ref(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v___y_3901_);
v_a_3925_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3913_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3913_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___boxed(lean_object* v_x_4133_, lean_object* v_y_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4133_, v_y_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr(lean_object* v_x_4141_, lean_object* v_y_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4141_, v_y_4142_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___boxed(lean_object* v_x_4152_, lean_object* v_y_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr(v_x_4152_, v_y_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
return v_res_4162_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = lean_box(0);
v___x_4167_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__1));
v___x_4168_ = l_Lean_mkConst(v___x_4167_, v___x_4166_);
return v___x_4168_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = lean_box(0);
v___x_4173_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__4));
v___x_4174_ = l_Lean_mkConst(v___x_4173_, v___x_4172_);
return v___x_4174_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__8(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = lean_box(0);
v___x_4179_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__7));
v___x_4180_ = l_Lean_mkConst(v___x_4179_, v___x_4178_);
return v___x_4180_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__11(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = lean_box(0);
v___x_4185_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__10));
v___x_4186_ = l_Lean_mkConst(v___x_4185_, v___x_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object* v_e_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_4194_ = lean_unsigned_to_nat(3u);
v___x_4195_ = l_Lean_Expr_isAppOfArity(v_e_4187_, v___x_4193_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_dec_ref(v_e_4187_);
v___x_4196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
else
{
lean_object* v___x_4198_; lean_object* v_x_4199_; lean_object* v_y_4200_; lean_object* v___x_4201_; 
v___x_4198_ = l_Lean_Expr_appFn_x21(v_e_4187_);
v_x_4199_ = l_Lean_Expr_appArg_x21(v___x_4198_);
lean_dec_ref(v___x_4198_);
v_y_4200_ = l_Lean_Expr_appArg_x21(v_e_4187_);
v___x_4201_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4199_, v_y_4200_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4326_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4326_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4326_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
if (lean_obj_tag(v_a_4202_) == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
lean_dec_ref(v_e_4187_);
v___x_4206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4206_);
v___x_4208_ = v___x_4204_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
else
{
lean_object* v_val_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4325_; 
v_val_4210_ = lean_ctor_get(v_a_4202_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v_a_4202_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4212_ = v_a_4202_;
v_isShared_4213_ = v_isSharedCheck_4325_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_val_4210_);
lean_dec(v_a_4202_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4325_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
switch(lean_obj_tag(v_val_4210_))
{
case 0:
{
uint8_t v_b_4214_; 
lean_del_object(v___x_4204_);
v_b_4214_ = lean_ctor_get_uint8(v_val_4210_, 0);
lean_dec_ref_known(v_val_4210_, 0);
if (v_b_4214_ == 0)
{
lean_object* v___x_4215_; 
lean_inc_ref(v_e_4187_);
v___x_4215_ = l_Lean_Meta_mkDecide(v_e_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___x_4218_ = l_Lean_Meta_mkEqRefl(v___x_4217_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4239_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4239_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4239_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4232_; 
v___x_4223_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__2, &l_Nat_reduceEqDiff___redArg___closed__2_once, _init_l_Nat_reduceEqDiff___redArg___closed__2);
v___x_4224_ = l_Lean_Expr_appArg_x21(v_a_4216_);
lean_dec(v_a_4216_);
v___x_4225_ = lean_mk_empty_array_with_capacity(v___x_4194_);
v___x_4226_ = lean_array_push(v___x_4225_, v_e_4187_);
v___x_4227_ = lean_array_push(v___x_4226_, v___x_4224_);
v___x_4228_ = lean_array_push(v___x_4227_, v_a_4219_);
v___x_4229_ = l_Lean_mkAppN(v___x_4223_, v___x_4228_);
lean_dec_ref(v___x_4228_);
v___x_4230_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4229_);
v___x_4232_ = v___x_4212_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4229_);
v___x_4232_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4233_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4233_, 0, v___x_4230_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
lean_ctor_set_uint8(v___x_4233_, sizeof(void*)*2, v___x_4195_);
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4234_);
v___x_4236_ = v___x_4221_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec(v_a_4216_);
lean_del_object(v___x_4212_);
lean_dec_ref(v_e_4187_);
v_a_4240_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4218_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4218_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_del_object(v___x_4212_);
lean_dec_ref(v_e_4187_);
v_a_4248_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4215_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4215_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v___x_4256_; 
lean_inc_ref(v_e_4187_);
v___x_4256_ = l_Lean_Meta_mkDecide(v_e_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
v___x_4258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___x_4259_ = l_Lean_Meta_mkEqRefl(v___x_4258_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4280_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4280_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4280_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4264_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__8, &l_Nat_reduceEqDiff___redArg___closed__8_once, _init_l_Nat_reduceEqDiff___redArg___closed__8);
v___x_4265_ = l_Lean_Expr_appArg_x21(v_a_4257_);
lean_dec(v_a_4257_);
v___x_4266_ = lean_mk_empty_array_with_capacity(v___x_4194_);
v___x_4267_ = lean_array_push(v___x_4266_, v_e_4187_);
v___x_4268_ = lean_array_push(v___x_4267_, v___x_4265_);
v___x_4269_ = lean_array_push(v___x_4268_, v_a_4260_);
v___x_4270_ = l_Lean_mkAppN(v___x_4264_, v___x_4269_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4270_);
v___x_4273_ = v___x_4212_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4270_);
v___x_4273_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4277_; 
v___x_4274_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4274_, 0, v___x_4271_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*2, v___x_4195_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___x_4275_);
v___x_4277_ = v___x_4262_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
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
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_a_4257_);
lean_del_object(v___x_4212_);
lean_dec_ref(v_e_4187_);
v_a_4281_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4259_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4259_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_del_object(v___x_4212_);
lean_dec_ref(v_e_4187_);
v_a_4289_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4256_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4256_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
case 1:
{
lean_object* v_p_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4312_; 
lean_dec_ref(v_e_4187_);
v_p_4297_ = lean_ctor_get(v_val_4210_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_val_4210_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4299_ = v_val_4210_;
v_isShared_4300_ = v_isSharedCheck_4312_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_p_4297_);
lean_dec(v_val_4210_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4312_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
v___x_4301_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v_p_4297_);
v___x_4303_ = v___x_4212_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_p_4297_);
v___x_4303_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4304_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4304_, 0, v___x_4301_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
lean_ctor_set_uint8(v___x_4304_, sizeof(void*)*2, v___x_4195_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4304_);
v___x_4306_ = v___x_4299_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4308_; 
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4306_);
v___x_4308_ = v___x_4204_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
default: 
{
lean_object* v_x_4313_; lean_object* v_y_4314_; lean_object* v_p_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
lean_dec_ref(v_e_4187_);
v_x_4313_ = lean_ctor_get(v_val_4210_, 0);
lean_inc_ref(v_x_4313_);
v_y_4314_ = lean_ctor_get(v_val_4210_, 1);
lean_inc_ref(v_y_4314_);
v_p_4315_ = lean_ctor_get(v_val_4210_, 2);
lean_inc_ref(v_p_4315_);
lean_dec_ref_known(v_val_4210_, 3);
v___x_4316_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(v_x_4313_, v_y_4314_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v_p_4315_);
v___x_4318_ = v___x_4212_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_p_4315_);
v___x_4318_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4319_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4319_, 0, v___x_4316_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
lean_ctor_set_uint8(v___x_4319_, sizeof(void*)*2, v___x_4195_);
v___x_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4320_);
v___x_4322_ = v___x_4204_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
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
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec_ref(v_e_4187_);
v_a_4327_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4201_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4201_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg___boxed(lean_object* v_e_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Nat_reduceEqDiff___redArg(v_e_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object* v_e_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Nat_reduceEqDiff___redArg(v_e_4342_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object* v_e_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Nat_reduceEqDiff(v_e_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4381_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4382_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4379_, v___x_4380_, v___x_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27____boxed(lean_object* v_a_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_();
return v_res_4384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4389_ = 1;
v___x_4390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_);
v___x_4391_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4388_, v___x_4389_, v___x_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29____boxed(lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_();
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_4395_; uint8_t v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_));
v___x_4396_ = 1;
v___x_4397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_);
v___x_4398_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4395_, v___x_4396_, v___x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31____boxed(lean_object* v_a_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_();
return v_res_4400_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = lean_box(0);
v___x_4407_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__1));
v___x_4408_ = l_Lean_mkConst(v___x_4407_, v___x_4406_);
return v___x_4408_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = lean_box(0);
v___x_4415_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__4));
v___x_4416_ = l_Lean_mkConst(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object* v_e_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4423_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_4424_ = lean_unsigned_to_nat(4u);
v___x_4425_ = l_Lean_Expr_isAppOfArity(v_e_4417_, v___x_4423_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
return v___x_4427_;
}
else
{
lean_object* v___x_4428_; lean_object* v_x_4429_; lean_object* v_y_4430_; lean_object* v___x_4431_; 
v___x_4428_ = l_Lean_Expr_appFn_x21(v_e_4417_);
v_x_4429_ = l_Lean_Expr_appArg_x21(v___x_4428_);
lean_dec_ref(v___x_4428_);
v_y_4430_ = l_Lean_Expr_appArg_x21(v_e_4417_);
lean_inc_ref(v_y_4430_);
lean_inc_ref(v_x_4429_);
v___x_4431_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4429_, v_y_4430_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4494_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4494_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4494_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___y_4437_; 
if (lean_obj_tag(v_a_4432_) == 0)
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
lean_del_object(v___x_4434_);
lean_dec_ref(v_y_4430_);
lean_dec_ref(v_x_4429_);
v___x_4444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
return v___x_4445_;
}
else
{
lean_object* v_val_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4493_; 
v_val_4446_ = lean_ctor_get(v_a_4432_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_a_4432_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4448_ = v_a_4432_;
v_isShared_4449_ = v_isSharedCheck_4493_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_val_4446_);
lean_dec(v_a_4432_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4493_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
switch(lean_obj_tag(v_val_4446_))
{
case 0:
{
uint8_t v_b_4450_; 
lean_del_object(v___x_4448_);
lean_dec_ref(v_y_4430_);
lean_dec_ref(v_x_4429_);
v_b_4450_ = lean_ctor_get_uint8(v_val_4446_, 0);
lean_dec_ref_known(v_val_4446_, 0);
if (v_b_4450_ == 0)
{
lean_object* v___x_4451_; 
v___x_4451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_4437_ = v___x_4451_;
goto v___jp_4436_;
}
else
{
lean_object* v___x_4452_; 
v___x_4452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___y_4437_ = v___x_4452_;
goto v___jp_4436_;
}
}
case 1:
{
lean_object* v_p_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4473_; 
lean_del_object(v___x_4434_);
v_p_4453_ = lean_ctor_get(v_val_4446_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_val_4446_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4455_ = v_val_4446_;
v_isShared_4456_ = v_isSharedCheck_4473_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_p_4453_);
lean_dec(v_val_4446_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4473_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4457_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__2, &l_Nat_reduceBeqDiff___redArg___closed__2_once, _init_l_Nat_reduceBeqDiff___redArg___closed__2);
v___x_4458_ = lean_unsigned_to_nat(3u);
v___x_4459_ = lean_mk_empty_array_with_capacity(v___x_4458_);
v___x_4460_ = lean_array_push(v___x_4459_, v_x_4429_);
v___x_4461_ = lean_array_push(v___x_4460_, v_y_4430_);
v___x_4462_ = lean_array_push(v___x_4461_, v_p_4453_);
v___x_4463_ = l_Lean_mkAppN(v___x_4457_, v___x_4462_);
lean_dec_ref(v___x_4462_);
v___x_4464_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4463_);
v___x_4466_ = v___x_4448_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4463_);
v___x_4466_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4467_, 0, v___x_4464_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
lean_ctor_set_uint8(v___x_4467_, sizeof(void*)*2, v___x_4425_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set_tag(v___x_4455_, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4467_);
v___x_4469_ = v___x_4455_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4470_; 
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
}
}
}
default: 
{
lean_object* v_x_4474_; lean_object* v_y_4475_; lean_object* v_p_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
lean_del_object(v___x_4434_);
v_x_4474_ = lean_ctor_get(v_val_4446_, 0);
lean_inc_ref_n(v_x_4474_, 2);
v_y_4475_ = lean_ctor_get(v_val_4446_, 1);
lean_inc_ref_n(v_y_4475_, 2);
v_p_4476_ = lean_ctor_get(v_val_4446_, 2);
lean_inc_ref(v_p_4476_);
lean_dec_ref_known(v_val_4446_, 3);
v___x_4477_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__5, &l_Nat_reduceBeqDiff___redArg___closed__5_once, _init_l_Nat_reduceBeqDiff___redArg___closed__5);
v___x_4478_ = lean_unsigned_to_nat(5u);
v___x_4479_ = lean_mk_empty_array_with_capacity(v___x_4478_);
v___x_4480_ = lean_array_push(v___x_4479_, v_x_4429_);
v___x_4481_ = lean_array_push(v___x_4480_, v_y_4430_);
v___x_4482_ = lean_array_push(v___x_4481_, v_x_4474_);
v___x_4483_ = lean_array_push(v___x_4482_, v_y_4475_);
v___x_4484_ = lean_array_push(v___x_4483_, v_p_4476_);
v___x_4485_ = l_Lean_mkAppN(v___x_4477_, v___x_4484_);
lean_dec_ref(v___x_4484_);
v___x_4486_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(v_x_4474_, v_y_4475_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4485_);
v___x_4488_ = v___x_4448_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4485_);
v___x_4488_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4489_, 0, v___x_4486_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
lean_ctor_set_uint8(v___x_4489_, sizeof(void*)*2, v___x_4425_);
v___x_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
v___x_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
return v___x_4491_;
}
}
}
}
}
v___jp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4438_ = lean_box(0);
lean_inc_ref(v___y_4437_);
v___x_4439_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4439_, 0, v___y_4437_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
lean_ctor_set_uint8(v___x_4439_, sizeof(void*)*2, v___x_4425_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4440_);
v___x_4442_ = v___x_4434_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec_ref(v_y_4430_);
lean_dec_ref(v_x_4429_);
v_a_4495_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4431_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4431_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object* v_e_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_Nat_reduceBeqDiff___redArg(v_e_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec_ref(v_e_4503_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object* v_e_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v___x_4519_; 
v___x_4519_ = l_Nat_reduceBeqDiff___redArg(v_e_4510_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object* v_e_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Nat_reduceBeqDiff(v_e_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_e_4520_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_));
v___x_4536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_));
v___x_4537_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4538_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4535_, v___x_4536_, v___x_4537_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27____boxed(lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_();
return v_res_4540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_4544_; uint8_t v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_));
v___x_4545_ = 1;
v___x_4546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_);
v___x_4547_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4544_, v___x_4545_, v___x_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29____boxed(lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_();
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_4551_; uint8_t v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_));
v___x_4552_ = 1;
v___x_4553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_);
v___x_4554_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4551_, v___x_4552_, v___x_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31____boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_();
return v_res_4556_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4562_ = lean_box(0);
v___x_4563_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__1));
v___x_4564_ = l_Lean_mkConst(v___x_4563_, v___x_4562_);
return v___x_4564_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = lean_box(0);
v___x_4571_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__4));
v___x_4572_ = l_Lean_mkConst(v___x_4571_, v___x_4570_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object* v_e_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; 
v___x_4579_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_4580_ = lean_unsigned_to_nat(4u);
v___x_4581_ = l_Lean_Expr_isAppOfArity(v_e_4573_, v___x_4579_, v___x_4580_);
if (v___x_4581_ == 0)
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
return v___x_4583_;
}
else
{
lean_object* v___x_4584_; lean_object* v_x_4585_; lean_object* v_y_4586_; lean_object* v___x_4587_; 
v___x_4584_ = l_Lean_Expr_appFn_x21(v_e_4573_);
v_x_4585_ = l_Lean_Expr_appArg_x21(v___x_4584_);
lean_dec_ref(v___x_4584_);
v_y_4586_ = l_Lean_Expr_appArg_x21(v_e_4573_);
lean_inc_ref(v_y_4586_);
lean_inc_ref(v_x_4585_);
v___x_4587_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg(v_x_4585_, v_y_4586_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4651_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4590_ = v___x_4587_;
v_isShared_4591_ = v_isSharedCheck_4651_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4587_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4651_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___y_4593_; 
if (lean_obj_tag(v_a_4588_) == 0)
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
lean_del_object(v___x_4590_);
lean_dec_ref(v_y_4586_);
lean_dec_ref(v_x_4585_);
v___x_4602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
else
{
lean_object* v_val_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4650_; 
v_val_4604_ = lean_ctor_get(v_a_4588_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_a_4588_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4606_ = v_a_4588_;
v_isShared_4607_ = v_isSharedCheck_4650_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_val_4604_);
lean_dec(v_a_4588_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4650_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
switch(lean_obj_tag(v_val_4604_))
{
case 0:
{
uint8_t v_b_4608_; 
lean_del_object(v___x_4606_);
lean_dec_ref(v_y_4586_);
lean_dec_ref(v_x_4585_);
v_b_4608_ = lean_ctor_get_uint8(v_val_4604_, 0);
lean_dec_ref_known(v_val_4604_, 0);
if (v_b_4608_ == 0)
{
if (v___x_4581_ == 0)
{
goto v___jp_4600_;
}
else
{
lean_object* v___x_4609_; 
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
v___y_4593_ = v___x_4609_;
goto v___jp_4592_;
}
}
else
{
goto v___jp_4600_;
}
}
case 1:
{
lean_object* v_p_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4630_; 
lean_del_object(v___x_4590_);
v_p_4610_ = lean_ctor_get(v_val_4604_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_val_4604_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4612_ = v_val_4604_;
v_isShared_4613_ = v_isSharedCheck_4630_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_p_4610_);
lean_dec(v_val_4604_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4630_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4614_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__2, &l_Nat_reduceBneDiff___redArg___closed__2_once, _init_l_Nat_reduceBneDiff___redArg___closed__2);
v___x_4615_ = lean_unsigned_to_nat(3u);
v___x_4616_ = lean_mk_empty_array_with_capacity(v___x_4615_);
v___x_4617_ = lean_array_push(v___x_4616_, v_x_4585_);
v___x_4618_ = lean_array_push(v___x_4617_, v_y_4586_);
v___x_4619_ = lean_array_push(v___x_4618_, v_p_4610_);
v___x_4620_ = l_Lean_mkAppN(v___x_4614_, v___x_4619_);
lean_dec_ref(v___x_4619_);
v___x_4621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__6);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4620_);
v___x_4623_ = v___x_4606_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4620_);
v___x_4623_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; lean_object* v___x_4626_; 
v___x_4624_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4624_, 0, v___x_4621_);
lean_ctor_set(v___x_4624_, 1, v___x_4623_);
lean_ctor_set_uint8(v___x_4624_, sizeof(void*)*2, v___x_4581_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set_tag(v___x_4612_, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4624_);
v___x_4626_ = v___x_4612_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4624_);
v___x_4626_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
lean_object* v___x_4627_; 
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4626_);
return v___x_4627_;
}
}
}
}
default: 
{
lean_object* v_x_4631_; lean_object* v_y_4632_; lean_object* v_p_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4645_; 
lean_del_object(v___x_4590_);
v_x_4631_ = lean_ctor_get(v_val_4604_, 0);
lean_inc_ref_n(v_x_4631_, 2);
v_y_4632_ = lean_ctor_get(v_val_4604_, 1);
lean_inc_ref_n(v_y_4632_, 2);
v_p_4633_ = lean_ctor_get(v_val_4604_, 2);
lean_inc_ref(v_p_4633_);
lean_dec_ref_known(v_val_4604_, 3);
v___x_4634_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__5, &l_Nat_reduceBneDiff___redArg___closed__5_once, _init_l_Nat_reduceBneDiff___redArg___closed__5);
v___x_4635_ = lean_unsigned_to_nat(5u);
v___x_4636_ = lean_mk_empty_array_with_capacity(v___x_4635_);
v___x_4637_ = lean_array_push(v___x_4636_, v_x_4585_);
v___x_4638_ = lean_array_push(v___x_4637_, v_y_4586_);
v___x_4639_ = lean_array_push(v___x_4638_, v_x_4631_);
v___x_4640_ = lean_array_push(v___x_4639_, v_y_4632_);
v___x_4641_ = lean_array_push(v___x_4640_, v_p_4633_);
v___x_4642_ = l_Lean_mkAppN(v___x_4634_, v___x_4641_);
lean_dec_ref(v___x_4641_);
v___x_4643_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(v_x_4631_, v_y_4632_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4642_);
v___x_4645_ = v___x_4606_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4642_);
v___x_4645_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4646_, 0, v___x_4643_);
lean_ctor_set(v___x_4646_, 1, v___x_4645_);
lean_ctor_set_uint8(v___x_4646_, sizeof(void*)*2, v___x_4581_);
v___x_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
return v___x_4648_;
}
}
}
}
}
v___jp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4594_ = lean_box(0);
lean_inc_ref(v___y_4593_);
v___x_4595_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4595_, 0, v___y_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2, v___x_4581_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4596_);
v___x_4598_ = v___x_4590_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
v___jp_4600_:
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBoolPred___redArg___closed__3);
v___y_4593_ = v___x_4601_;
goto v___jp_4592_;
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec_ref(v_y_4586_);
lean_dec_ref(v_x_4585_);
v_a_4652_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4587_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4587_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object* v_e_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_Nat_reduceBneDiff___redArg(v_e_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec_ref(v_e_4660_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object* v_e_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Nat_reduceBneDiff___redArg(v_e_4667_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object* v_e_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l_Nat_reduceBneDiff(v_e_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_e_4677_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_));
v___x_4693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_));
v___x_4694_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4695_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4692_, v___x_4693_, v___x_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27____boxed(lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_();
return v_res_4697_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_));
v___x_4702_ = 1;
v___x_4703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_);
v___x_4704_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4701_, v___x_4702_, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29____boxed(lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_();
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_4708_; uint8_t v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_));
v___x_4709_ = 1;
v___x_4710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_);
v___x_4711_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4708_, v___x_4709_, v___x_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31____boxed(lean_object* v_a_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_();
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(lean_object* v_nm_4744_, lean_object* v_arity_4745_, uint8_t v_isLT_4746_, lean_object* v_e_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; uint8_t v___x_4785_; 
v___x_4785_ = l_Lean_Expr_isAppOfArity(v_e_4747_, v_nm_4744_, v_arity_4745_);
if (v___x_4785_ == 0)
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
lean_dec_ref(v_e_4747_);
v___x_4786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
return v___x_4787_;
}
else
{
lean_object* v___x_4788_; lean_object* v_x_4789_; lean_object* v_y_4790_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v_leLvl_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4933_; 
v___x_4788_ = l_Lean_Expr_appFn_x21(v_e_4747_);
v_x_4789_ = l_Lean_Expr_appArg_x21(v___x_4788_);
lean_dec_ref(v___x_4788_);
v_y_4790_ = l_Lean_Expr_appArg_x21(v_e_4747_);
if (v_isLT_4746_ == 0)
{
lean_object* v___x_4986_; 
v___x_4986_ = lean_unsigned_to_nat(0u);
v___y_4933_ = v___x_4986_;
goto v___jp_4932_;
}
else
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_unsigned_to_nat(1u);
v___y_4933_ = v___x_4987_;
goto v___jp_4932_;
}
v___jp_4791_:
{
if (lean_obj_tag(v___y_4792_) == 0)
{
lean_dec_ref(v_y_4790_);
if (lean_obj_tag(v___y_4793_) == 0)
{
lean_object* v_n_4799_; lean_object* v_n_4800_; uint8_t v___x_4801_; lean_object* v___x_4802_; 
lean_dec_ref(v_x_4789_);
v_n_4799_ = lean_ctor_get(v___y_4792_, 0);
lean_inc(v_n_4799_);
lean_dec_ref_known(v___y_4792_, 1);
v_n_4800_ = lean_ctor_get(v___y_4793_, 0);
lean_inc(v_n_4800_);
lean_dec_ref_known(v___y_4793_, 1);
v___x_4801_ = lean_nat_dec_le(v_n_4799_, v_n_4800_);
lean_dec(v_n_4800_);
lean_dec(v_n_4799_);
v___x_4802_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_4747_, v___x_4801_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
return v___x_4802_;
}
else
{
lean_object* v_n_4803_; lean_object* v_e_4804_; lean_object* v_o_4805_; lean_object* v_n_4806_; uint8_t v___x_4807_; 
lean_dec_ref(v_e_4747_);
v_n_4803_ = lean_ctor_get(v___y_4792_, 0);
lean_inc(v_n_4803_);
lean_dec_ref_known(v___y_4792_, 1);
v_e_4804_ = lean_ctor_get(v___y_4793_, 0);
lean_inc_ref(v_e_4804_);
v_o_4805_ = lean_ctor_get(v___y_4793_, 1);
lean_inc_ref(v_o_4805_);
v_n_4806_ = lean_ctor_get(v___y_4793_, 2);
lean_inc(v_n_4806_);
lean_dec_ref_known(v___y_4793_, 3);
v___x_4807_ = lean_nat_dec_le(v_n_4803_, v_n_4806_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4808_ = lean_nat_sub(v_n_4803_, v_n_4806_);
lean_dec(v_n_4806_);
lean_dec(v_n_4803_);
v___x_4809_ = l_Lean_mkNatLit(v___x_4808_);
lean_inc_ref(v_e_4804_);
lean_inc_n(v_leLvl_4794_, 2);
v___x_4810_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v___x_4809_, v_e_4804_);
lean_inc_ref(v_x_4789_);
lean_inc_ref(v_o_4805_);
v___x_4811_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v_o_4805_, v_x_4789_);
v___x_4812_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4811_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc(v_a_4813_);
lean_dec_ref_known(v___x_4812_, 1);
v___x_4814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__3));
v___x_4815_ = lean_unsigned_to_nat(4u);
v___x_4816_ = lean_mk_empty_array_with_capacity(v___x_4815_);
v___x_4817_ = lean_array_push(v___x_4816_, v_x_4789_);
v___x_4818_ = lean_array_push(v___x_4817_, v_e_4804_);
v___x_4819_ = lean_array_push(v___x_4818_, v_o_4805_);
v___x_4820_ = lean_array_push(v___x_4819_, v_a_4813_);
v___x_4821_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_4810_, v___x_4814_, v___x_4820_, v___y_4798_);
lean_dec_ref(v___x_4820_);
return v___x_4821_;
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v___x_4810_);
lean_dec_ref(v_o_4805_);
lean_dec_ref(v_e_4804_);
lean_dec_ref(v_x_4789_);
v_a_4822_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4812_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4812_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
lean_dec(v_n_4806_);
lean_dec(v_n_4803_);
lean_inc_ref(v_o_4805_);
lean_inc_ref(v_x_4789_);
lean_inc(v_leLvl_4794_);
v___x_4830_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v_x_4789_, v_o_4805_);
v___x_4831_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4830_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref_known(v___x_4831_, 1);
v___x_4833_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_4834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__5));
v___x_4835_ = lean_unsigned_to_nat(4u);
v___x_4836_ = lean_mk_empty_array_with_capacity(v___x_4835_);
v___x_4837_ = lean_array_push(v___x_4836_, v_x_4789_);
v___x_4838_ = lean_array_push(v___x_4837_, v_e_4804_);
v___x_4839_ = lean_array_push(v___x_4838_, v_o_4805_);
v___x_4840_ = lean_array_push(v___x_4839_, v_a_4832_);
v___x_4841_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_4833_, v___x_4834_, v___x_4840_, v___y_4798_);
lean_dec_ref(v___x_4840_);
return v___x_4841_;
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec_ref(v_o_4805_);
lean_dec_ref(v_e_4804_);
lean_dec_ref(v_x_4789_);
v_a_4842_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4831_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4831_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_e_4747_);
if (lean_obj_tag(v___y_4793_) == 0)
{
lean_object* v_e_4850_; lean_object* v_o_4851_; lean_object* v_n_4852_; lean_object* v_n_4853_; uint8_t v___x_4854_; 
v_e_4850_ = lean_ctor_get(v___y_4792_, 0);
lean_inc_ref(v_e_4850_);
v_o_4851_ = lean_ctor_get(v___y_4792_, 1);
lean_inc_ref(v_o_4851_);
v_n_4852_ = lean_ctor_get(v___y_4792_, 2);
lean_inc(v_n_4852_);
lean_dec_ref_known(v___y_4792_, 3);
v_n_4853_ = lean_ctor_get(v___y_4793_, 0);
lean_inc(v_n_4853_);
lean_dec_ref_known(v___y_4793_, 1);
v___x_4854_ = lean_nat_dec_le(v_n_4852_, v_n_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
lean_dec(v_n_4853_);
lean_dec(v_n_4852_);
lean_inc_ref(v_o_4851_);
lean_inc_ref(v_y_4790_);
lean_inc(v_leLvl_4794_);
v___x_4855_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_leLvl_4794_, v_y_4790_, v_o_4851_);
v___x_4856_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4855_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc(v_a_4857_);
lean_dec_ref_known(v___x_4856_, 1);
v___x_4858_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_4859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__7));
v___x_4860_ = lean_unsigned_to_nat(4u);
v___x_4861_ = lean_mk_empty_array_with_capacity(v___x_4860_);
v___x_4862_ = lean_array_push(v___x_4861_, v_e_4850_);
v___x_4863_ = lean_array_push(v___x_4862_, v_o_4851_);
v___x_4864_ = lean_array_push(v___x_4863_, v_y_4790_);
v___x_4865_ = lean_array_push(v___x_4864_, v_a_4857_);
v___x_4866_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_4858_, v___x_4859_, v___x_4865_, v___y_4798_);
lean_dec_ref(v___x_4865_);
return v___x_4866_;
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
lean_dec_ref(v_o_4851_);
lean_dec_ref(v_e_4850_);
lean_dec_ref(v_y_4790_);
v_a_4867_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4856_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4856_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4875_ = lean_nat_sub(v_n_4853_, v_n_4852_);
lean_dec(v_n_4852_);
lean_dec(v_n_4853_);
v___x_4876_ = l_Lean_mkNatLit(v___x_4875_);
lean_inc_ref(v_e_4850_);
lean_inc_n(v_leLvl_4794_, 2);
v___x_4877_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v_e_4850_, v___x_4876_);
lean_inc_ref(v_y_4790_);
lean_inc_ref(v_o_4851_);
v___x_4878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v_o_4851_, v_y_4790_);
v___x_4879_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4878_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4879_, 1);
v___x_4881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__9));
v___x_4882_ = lean_unsigned_to_nat(4u);
v___x_4883_ = lean_mk_empty_array_with_capacity(v___x_4882_);
v___x_4884_ = lean_array_push(v___x_4883_, v_e_4850_);
v___x_4885_ = lean_array_push(v___x_4884_, v_o_4851_);
v___x_4886_ = lean_array_push(v___x_4885_, v_y_4790_);
v___x_4887_ = lean_array_push(v___x_4886_, v_a_4880_);
v___x_4888_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_4877_, v___x_4881_, v___x_4887_, v___y_4798_);
lean_dec_ref(v___x_4887_);
return v___x_4888_;
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
lean_dec_ref(v___x_4877_);
lean_dec_ref(v_o_4851_);
lean_dec_ref(v_e_4850_);
lean_dec_ref(v_y_4790_);
v_a_4889_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4879_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4879_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
else
{
lean_object* v_e_4897_; lean_object* v_o_4898_; lean_object* v_n_4899_; lean_object* v_e_4900_; lean_object* v_o_4901_; lean_object* v_n_4902_; uint8_t v___x_4903_; 
lean_dec_ref(v_y_4790_);
v_e_4897_ = lean_ctor_get(v___y_4792_, 0);
lean_inc_ref(v_e_4897_);
v_o_4898_ = lean_ctor_get(v___y_4792_, 1);
lean_inc_ref(v_o_4898_);
v_n_4899_ = lean_ctor_get(v___y_4792_, 2);
lean_inc(v_n_4899_);
lean_dec_ref_known(v___y_4792_, 3);
v_e_4900_ = lean_ctor_get(v___y_4793_, 0);
lean_inc_ref(v_e_4900_);
v_o_4901_ = lean_ctor_get(v___y_4793_, 1);
lean_inc_ref(v_o_4901_);
v_n_4902_ = lean_ctor_get(v___y_4793_, 2);
lean_inc(v_n_4902_);
lean_dec_ref_known(v___y_4793_, 3);
v___x_4903_ = lean_nat_dec_le(v_n_4899_, v_n_4902_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4904_ = lean_nat_sub(v_n_4899_, v_n_4902_);
lean_dec(v_n_4902_);
lean_dec(v_n_4899_);
v___x_4905_ = l_Lean_mkNatLit(v___x_4904_);
lean_inc_ref(v_e_4897_);
v___x_4906_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4897_, v___x_4905_);
lean_inc_ref(v_e_4900_);
lean_inc_n(v_leLvl_4794_, 2);
v___x_4907_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v___x_4906_, v_e_4900_);
lean_inc_ref(v_o_4898_);
lean_inc_ref(v_o_4901_);
v___x_4908_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_4794_, v_o_4901_, v_o_4898_);
v___x_4909_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4908_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4909_, 1);
v___x_4911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__11));
v___x_4912_ = lean_unsigned_to_nat(5u);
v___x_4913_ = lean_mk_empty_array_with_capacity(v___x_4912_);
v___x_4914_ = lean_array_push(v___x_4913_, v_e_4897_);
v___x_4915_ = lean_array_push(v___x_4914_, v_e_4900_);
v___x_4916_ = lean_array_push(v___x_4915_, v_o_4898_);
v___x_4917_ = lean_array_push(v___x_4916_, v_o_4901_);
v___x_4918_ = lean_array_push(v___x_4917_, v_a_4910_);
v___x_4919_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_4907_, v___x_4911_, v___x_4918_, v___y_4798_);
lean_dec_ref(v___x_4918_);
return v___x_4919_;
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
lean_dec_ref(v___x_4907_);
lean_dec_ref(v_o_4901_);
lean_dec_ref(v_e_4900_);
lean_dec_ref(v_o_4898_);
lean_dec_ref(v_e_4897_);
v_a_4920_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4909_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4909_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
else
{
uint8_t v___x_4928_; 
v___x_4928_ = lean_nat_dec_eq(v_n_4899_, v_n_4902_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4929_ = lean_nat_sub(v_n_4902_, v_n_4899_);
lean_dec(v_n_4899_);
lean_dec(v_n_4902_);
v___x_4930_ = l_Lean_mkNatLit(v___x_4929_);
lean_inc_ref(v_e_4900_);
v___x_4931_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4900_, v___x_4930_);
v___y_4754_ = v_e_4897_;
v___y_4755_ = v___y_4798_;
v___y_4756_ = v_o_4901_;
v___y_4757_ = v_leLvl_4794_;
v___y_4758_ = v___y_4796_;
v___y_4759_ = v___y_4797_;
v___y_4760_ = v___y_4795_;
v___y_4761_ = v_o_4898_;
v___y_4762_ = v_e_4900_;
v___y_4763_ = v___x_4931_;
goto v___jp_4753_;
}
else
{
lean_dec(v_n_4902_);
lean_dec(v_n_4899_);
lean_inc_ref(v_e_4900_);
v___y_4754_ = v_e_4897_;
v___y_4755_ = v___y_4798_;
v___y_4756_ = v_o_4901_;
v___y_4757_ = v_leLvl_4794_;
v___y_4758_ = v___y_4796_;
v___y_4759_ = v___y_4797_;
v___y_4760_ = v___y_4795_;
v___y_4761_ = v_o_4898_;
v___y_4762_ = v_e_4900_;
v___y_4763_ = v_e_4900_;
goto v___jp_4753_;
}
}
}
}
}
v___jp_4932_:
{
lean_object* v___x_4934_; 
lean_inc_ref(v_x_4789_);
v___x_4934_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_4789_, v___y_4933_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4977_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4937_ = v___x_4934_;
v_isShared_4938_ = v_isSharedCheck_4977_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4934_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4977_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
if (lean_obj_tag(v_a_4935_) == 1)
{
lean_object* v_val_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
lean_del_object(v___x_4937_);
v_val_4939_ = lean_ctor_get(v_a_4935_, 0);
lean_inc(v_val_4939_);
lean_dec_ref_known(v_a_4935_, 1);
v___x_4940_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_y_4790_);
v___x_4941_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_4790_, v___x_4940_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4964_; 
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4944_ = v___x_4941_;
v_isShared_4945_ = v_isSharedCheck_4964_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4941_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4964_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
if (lean_obj_tag(v_a_4942_) == 1)
{
lean_object* v_val_4946_; lean_object* v___x_4947_; 
lean_del_object(v___x_4944_);
v_val_4946_ = lean_ctor_get(v_a_4942_, 0);
lean_inc(v_val_4946_);
lean_dec_ref_known(v_a_4942_, 1);
v___x_4947_ = l_Lean_leCarrierIsSort(v_a_4750_, v_a_4751_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v_a_4948_; uint8_t v___x_4949_; 
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
lean_inc(v_a_4948_);
lean_dec_ref_known(v___x_4947_, 1);
v___x_4949_ = lean_unbox(v_a_4948_);
lean_dec(v_a_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; 
v___x_4950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14);
v___y_4792_ = v_val_4939_;
v___y_4793_ = v_val_4946_;
v_leLvl_4794_ = v___x_4950_;
v___y_4795_ = v_a_4748_;
v___y_4796_ = v_a_4749_;
v___y_4797_ = v_a_4750_;
v___y_4798_ = v_a_4751_;
goto v___jp_4791_;
}
else
{
lean_object* v___x_4951_; 
v___x_4951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15);
v___y_4792_ = v_val_4939_;
v___y_4793_ = v_val_4946_;
v_leLvl_4794_ = v___x_4951_;
v___y_4795_ = v_a_4748_;
v___y_4796_ = v_a_4749_;
v___y_4797_ = v_a_4750_;
v___y_4798_ = v_a_4751_;
goto v___jp_4791_;
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v_val_4946_);
lean_dec(v_val_4939_);
lean_dec_ref(v_y_4790_);
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_e_4747_);
v_a_4952_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4947_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4947_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
else
{
lean_object* v___x_4960_; lean_object* v___x_4962_; 
lean_dec(v_a_4942_);
lean_dec(v_val_4939_);
lean_dec_ref(v_y_4790_);
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_e_4747_);
v___x_4960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v___x_4960_);
v___x_4962_ = v___x_4944_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4960_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
else
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
lean_dec(v_val_4939_);
lean_dec_ref(v_y_4790_);
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_e_4747_);
v_a_4965_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4967_ = v___x_4941_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4941_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
else
{
lean_object* v___x_4973_; lean_object* v___x_4975_; 
lean_dec(v_a_4935_);
lean_dec_ref(v_y_4790_);
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_e_4747_);
v___x_4973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 0, v___x_4973_);
v___x_4975_ = v___x_4937_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4973_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
else
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
lean_dec_ref(v_y_4790_);
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_e_4747_);
v_a_4978_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4934_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4934_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
v___jp_4753_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_inc_ref(v___y_4754_);
lean_inc_n(v___y_4757_, 2);
v___x_4764_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_4757_, v___y_4754_, v___y_4763_);
lean_inc_ref(v___y_4756_);
lean_inc_ref(v___y_4761_);
v___x_4765_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_4757_, v___y_4761_, v___y_4756_);
v___x_4766_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4765_, v___y_4760_, v___y_4758_, v___y_4759_, v___y_4755_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref_known(v___x_4766_, 1);
v___x_4768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___closed__1));
v___x_4769_ = lean_unsigned_to_nat(5u);
v___x_4770_ = lean_mk_empty_array_with_capacity(v___x_4769_);
v___x_4771_ = lean_array_push(v___x_4770_, v___y_4754_);
v___x_4772_ = lean_array_push(v___x_4771_, v___y_4762_);
v___x_4773_ = lean_array_push(v___x_4772_, v___y_4761_);
v___x_4774_ = lean_array_push(v___x_4773_, v___y_4756_);
v___x_4775_ = lean_array_push(v___x_4774_, v_a_4767_);
v___x_4776_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_4764_, v___x_4768_, v___x_4775_, v___y_4755_);
lean_dec_ref(v___x_4775_);
return v___x_4776_;
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
lean_dec_ref(v___x_4764_);
lean_dec_ref(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec_ref(v___y_4756_);
lean_dec_ref(v___y_4754_);
v_a_4777_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4766_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4766_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg___boxed(lean_object* v_nm_4988_, lean_object* v_arity_4989_, lean_object* v_isLT_4990_, lean_object* v_e_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_){
_start:
{
uint8_t v_isLT_boxed_4997_; lean_object* v_res_4998_; 
v_isLT_boxed_4997_ = lean_unbox(v_isLT_4990_);
v_res_4998_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(v_nm_4988_, v_arity_4989_, v_isLT_boxed_4997_, v_e_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_nm_4988_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE(lean_object* v_nm_4999_, lean_object* v_arity_5000_, uint8_t v_isLT_5001_, lean_object* v_e_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v___x_5011_; 
v___x_5011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(v_nm_4999_, v_arity_5000_, v_isLT_5001_, v_e_5002_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
return v___x_5011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___boxed(lean_object* v_nm_5012_, lean_object* v_arity_5013_, lean_object* v_isLT_5014_, lean_object* v_e_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
uint8_t v_isLT_boxed_5024_; lean_object* v_res_5025_; 
v_isLT_boxed_5024_ = lean_unbox(v_isLT_5014_);
v_res_5025_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE(v_nm_5012_, v_arity_5013_, v_isLT_boxed_5024_, v_e_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
lean_dec(v_a_5022_);
lean_dec_ref(v_a_5021_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
lean_dec(v_a_5016_);
lean_dec(v_nm_5012_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object* v_e_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; uint8_t v___x_5034_; lean_object* v___x_5035_; 
v___x_5032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_5033_ = lean_unsigned_to_nat(4u);
v___x_5034_ = 0;
v___x_5035_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLTLE___redArg(v___x_5032_, v___x_5033_, v___x_5034_, v_e_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg___boxed(lean_object* v_e_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Nat_reduceLeDiff___redArg(v_e_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object* v_e_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Nat_reduceLeDiff___redArg(v_e_5043_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object* v_e_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Nat_reduceLeDiff(v_e_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5083_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5084_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5081_, v___x_5082_, v___x_5083_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27____boxed(lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_();
return v_res_5086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5087_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_5090_; uint8_t v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5091_ = 1;
v___x_5092_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_);
v___x_5093_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5090_, v___x_5091_, v___x_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29____boxed(lean_object* v_a_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_();
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_5097_; uint8_t v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_));
v___x_5098_ = 1;
v___x_5099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_);
v___x_5100_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5097_, v___x_5098_, v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31____boxed(lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_();
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object* v_e_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v___y_5134_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v___x_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5165_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_5166_ = lean_unsigned_to_nat(6u);
v___x_5167_ = l_Lean_Expr_isAppOfArity(v_e_5127_, v___x_5165_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
v___x_5169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5168_);
return v___x_5169_;
}
else
{
lean_object* v___x_5170_; lean_object* v_p_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5170_ = l_Lean_Expr_appFn_x21(v_e_5127_);
v_p_5171_ = l_Lean_Expr_appArg_x21(v___x_5170_);
lean_dec_ref(v___x_5170_);
v___x_5172_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_5171_);
v___x_5173_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_p_5171_, v___x_5172_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5366_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5176_ = v___x_5173_;
v_isShared_5177_ = v_isSharedCheck_5366_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5173_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5366_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
if (lean_obj_tag(v_a_5174_) == 1)
{
lean_object* v_val_5178_; lean_object* v___x_5179_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; lean_object* v___y_5185_; lean_object* v___y_5186_; lean_object* v___y_5187_; lean_object* v___y_5188_; lean_object* v___x_5208_; 
lean_del_object(v___x_5176_);
v_val_5178_ = lean_ctor_get(v_a_5174_, 0);
lean_inc(v_val_5178_);
lean_dec_ref_known(v_a_5174_, 1);
v___x_5179_ = l_Lean_Expr_appArg_x21(v_e_5127_);
lean_inc_ref(v___x_5179_);
v___x_5208_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v___x_5179_, v___x_5172_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5353_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5211_ = v___x_5208_;
v_isShared_5212_ = v_isSharedCheck_5353_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5208_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5353_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
if (lean_obj_tag(v_a_5209_) == 1)
{
lean_object* v_val_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5348_; 
lean_del_object(v___x_5211_);
v_val_5213_ = lean_ctor_get(v_a_5209_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v_a_5209_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5215_ = v_a_5209_;
v_isShared_5216_ = v_isSharedCheck_5348_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_val_5213_);
lean_dec(v_a_5209_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5348_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_Lean_leCarrierIsSort(v_a_5130_, v_a_5131_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v_leLvl_5220_; lean_object* v___y_5221_; lean_object* v___y_5222_; lean_object* v___y_5223_; lean_object* v___y_5224_; uint8_t v___x_5337_; 
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5217_, 1);
v___x_5337_ = lean_unbox(v_a_5218_);
lean_dec(v_a_5218_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; 
v___x_5338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__14);
v_leLvl_5220_ = v___x_5338_;
v___y_5221_ = v_a_5128_;
v___y_5222_ = v_a_5129_;
v___y_5223_ = v_a_5130_;
v___y_5224_ = v_a_5131_;
goto v___jp_5219_;
}
else
{
lean_object* v___x_5339_; 
v___x_5339_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceNatEqExpr___redArg___closed__15);
v_leLvl_5220_ = v___x_5339_;
v___y_5221_ = v_a_5128_;
v___y_5222_ = v_a_5129_;
v___y_5223_ = v_a_5130_;
v___y_5224_ = v_a_5131_;
goto v___jp_5219_;
}
v___jp_5219_:
{
if (lean_obj_tag(v_val_5178_) == 0)
{
lean_dec_ref(v___x_5179_);
if (lean_obj_tag(v_val_5213_) == 0)
{
lean_object* v_n_5225_; lean_object* v_n_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5256_; 
lean_dec_ref(v_p_5171_);
v_n_5225_ = lean_ctor_get(v_val_5178_, 0);
lean_inc(v_n_5225_);
lean_dec_ref_known(v_val_5178_, 1);
v_n_5226_ = lean_ctor_get(v_val_5213_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_val_5213_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5228_ = v_val_5213_;
v_isShared_5229_ = v_isSharedCheck_5256_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_n_5226_);
lean_dec(v_val_5213_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5256_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; 
v___x_5230_ = lean_nat_sub(v_n_5225_, v_n_5226_);
lean_dec(v_n_5226_);
lean_dec(v_n_5225_);
v___x_5231_ = l_Lean_mkNatLit(v___x_5230_);
lean_inc_ref(v___x_5231_);
v___x_5232_ = l_Lean_Meta_mkEqRefl(v___x_5231_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5247_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5235_ = v___x_5232_;
v_isShared_5236_ = v_isSharedCheck_5247_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5232_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5247_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 0, v_a_5233_);
v___x_5238_ = v___x_5215_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
lean_object* v___x_5239_; lean_object* v___x_5241_; 
v___x_5239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5239_, 0, v___x_5231_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
lean_ctor_set_uint8(v___x_5239_, sizeof(void*)*2, v___x_5167_);
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v___x_5239_);
v___x_5241_ = v___x_5228_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
lean_object* v___x_5243_; 
if (v_isShared_5236_ == 0)
{
lean_ctor_set(v___x_5235_, 0, v___x_5241_);
v___x_5243_ = v___x_5235_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec_ref(v___x_5231_);
lean_del_object(v___x_5228_);
lean_del_object(v___x_5215_);
v_a_5248_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5232_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5232_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
else
{
lean_object* v_n_5257_; lean_object* v_e_5258_; lean_object* v_o_5259_; lean_object* v_n_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
lean_del_object(v___x_5215_);
v_n_5257_ = lean_ctor_get(v_val_5178_, 0);
lean_inc(v_n_5257_);
lean_dec_ref_known(v_val_5178_, 1);
v_e_5258_ = lean_ctor_get(v_val_5213_, 0);
lean_inc_ref_n(v_e_5258_, 2);
v_o_5259_ = lean_ctor_get(v_val_5213_, 1);
lean_inc_ref(v_o_5259_);
v_n_5260_ = lean_ctor_get(v_val_5213_, 2);
lean_inc(v_n_5260_);
lean_dec_ref_known(v_val_5213_, 3);
v___x_5261_ = lean_nat_sub(v_n_5257_, v_n_5260_);
lean_dec(v_n_5260_);
lean_dec(v_n_5257_);
v___x_5262_ = l_Lean_mkNatLit(v___x_5261_);
v___x_5263_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5262_, v_e_5258_);
v___x_5264_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__5));
v___x_5265_ = lean_unsigned_to_nat(3u);
v___x_5266_ = lean_mk_empty_array_with_capacity(v___x_5265_);
v___x_5267_ = lean_array_push(v___x_5266_, v_p_5171_);
v___x_5268_ = lean_array_push(v___x_5267_, v_e_5258_);
v___x_5269_ = lean_array_push(v___x_5268_, v_o_5259_);
v___x_5270_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5263_, v___x_5264_, v___x_5269_, v___y_5224_);
lean_dec_ref(v___x_5269_);
return v___x_5270_;
}
}
else
{
lean_del_object(v___x_5215_);
lean_dec_ref(v_p_5171_);
if (lean_obj_tag(v_val_5213_) == 0)
{
lean_object* v_e_5271_; lean_object* v_o_5272_; lean_object* v_n_5273_; lean_object* v_n_5274_; uint8_t v___x_5275_; 
v_e_5271_ = lean_ctor_get(v_val_5178_, 0);
lean_inc_ref(v_e_5271_);
v_o_5272_ = lean_ctor_get(v_val_5178_, 1);
lean_inc_ref(v_o_5272_);
v_n_5273_ = lean_ctor_get(v_val_5178_, 2);
lean_inc(v_n_5273_);
lean_dec_ref_known(v_val_5178_, 3);
v_n_5274_ = lean_ctor_get(v_val_5213_, 0);
lean_inc(v_n_5274_);
lean_dec_ref_known(v_val_5213_, 1);
v___x_5275_ = lean_nat_dec_le(v_n_5273_, v_n_5274_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
lean_inc_ref(v_o_5272_);
lean_inc_ref(v___x_5179_);
lean_inc(v_leLvl_5220_);
v___x_5276_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_5220_, v___x_5179_, v_o_5272_);
v___x_5277_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5276_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc(v_a_5278_);
lean_dec_ref_known(v___x_5277_, 1);
v___x_5279_ = lean_nat_sub(v_n_5273_, v_n_5274_);
lean_dec(v_n_5274_);
lean_dec(v_n_5273_);
v___x_5280_ = l_Lean_mkNatLit(v___x_5279_);
lean_inc_ref(v_e_5271_);
v___x_5281_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5271_, v___x_5280_);
v___x_5282_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__7));
v___x_5283_ = lean_unsigned_to_nat(4u);
v___x_5284_ = lean_mk_empty_array_with_capacity(v___x_5283_);
v___x_5285_ = lean_array_push(v___x_5284_, v_o_5272_);
v___x_5286_ = lean_array_push(v___x_5285_, v___x_5179_);
v___x_5287_ = lean_array_push(v___x_5286_, v_a_5278_);
v___x_5288_ = lean_array_push(v___x_5287_, v_e_5271_);
v___x_5289_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5281_, v___x_5282_, v___x_5288_, v___y_5224_);
lean_dec_ref(v___x_5288_);
return v___x_5289_;
}
else
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
lean_dec(v_n_5274_);
lean_dec(v_n_5273_);
lean_dec_ref(v_o_5272_);
lean_dec_ref(v_e_5271_);
lean_dec_ref(v___x_5179_);
v_a_5290_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___x_5277_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5277_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
else
{
uint8_t v___x_5298_; 
v___x_5298_ = lean_nat_dec_eq(v_n_5273_, v_n_5274_);
if (v___x_5298_ == 0)
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5299_ = lean_nat_sub(v_n_5274_, v_n_5273_);
lean_dec(v_n_5273_);
lean_dec(v_n_5274_);
v___x_5300_ = l_Lean_mkNatLit(v___x_5299_);
lean_inc_ref(v_e_5271_);
v___x_5301_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5271_, v___x_5300_);
v___y_5181_ = v_e_5271_;
v___y_5182_ = v___y_5222_;
v___y_5183_ = v___y_5224_;
v___y_5184_ = v___y_5223_;
v___y_5185_ = v___y_5221_;
v___y_5186_ = v_o_5272_;
v___y_5187_ = v_leLvl_5220_;
v___y_5188_ = v___x_5301_;
goto v___jp_5180_;
}
else
{
lean_dec(v_n_5274_);
lean_dec(v_n_5273_);
lean_inc_ref(v_e_5271_);
v___y_5181_ = v_e_5271_;
v___y_5182_ = v___y_5222_;
v___y_5183_ = v___y_5224_;
v___y_5184_ = v___y_5223_;
v___y_5185_ = v___y_5221_;
v___y_5186_ = v_o_5272_;
v___y_5187_ = v_leLvl_5220_;
v___y_5188_ = v_e_5271_;
goto v___jp_5180_;
}
}
}
else
{
lean_object* v_e_5302_; lean_object* v_o_5303_; lean_object* v_n_5304_; lean_object* v_e_5305_; lean_object* v_o_5306_; lean_object* v_n_5307_; uint8_t v___x_5308_; 
lean_dec_ref(v___x_5179_);
v_e_5302_ = lean_ctor_get(v_val_5178_, 0);
lean_inc_ref(v_e_5302_);
v_o_5303_ = lean_ctor_get(v_val_5178_, 1);
lean_inc_ref(v_o_5303_);
v_n_5304_ = lean_ctor_get(v_val_5178_, 2);
lean_inc(v_n_5304_);
lean_dec_ref_known(v_val_5178_, 3);
v_e_5305_ = lean_ctor_get(v_val_5213_, 0);
lean_inc_ref(v_e_5305_);
v_o_5306_ = lean_ctor_get(v_val_5213_, 1);
lean_inc_ref(v_o_5306_);
v_n_5307_ = lean_ctor_get(v_val_5213_, 2);
lean_inc(v_n_5307_);
lean_dec_ref_known(v_val_5213_, 3);
v___x_5308_ = lean_nat_dec_le(v_n_5304_, v_n_5307_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; lean_object* v___x_5310_; 
lean_inc_ref(v_o_5303_);
lean_inc_ref(v_o_5306_);
lean_inc(v_leLvl_5220_);
v___x_5309_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_leLvl_5220_, v_o_5306_, v_o_5303_);
v___x_5310_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5309_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
lean_inc(v_a_5311_);
lean_dec_ref_known(v___x_5310_, 1);
v___x_5312_ = lean_nat_sub(v_n_5304_, v_n_5307_);
lean_dec(v_n_5307_);
lean_dec(v_n_5304_);
v___x_5313_ = l_Lean_mkNatLit(v___x_5312_);
lean_inc_ref(v_e_5302_);
v___x_5314_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5302_, v___x_5313_);
lean_inc_ref(v_e_5305_);
v___x_5315_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5314_, v_e_5305_);
v___x_5316_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__9));
v___x_5317_ = lean_unsigned_to_nat(5u);
v___x_5318_ = lean_mk_empty_array_with_capacity(v___x_5317_);
v___x_5319_ = lean_array_push(v___x_5318_, v_e_5302_);
v___x_5320_ = lean_array_push(v___x_5319_, v_e_5305_);
v___x_5321_ = lean_array_push(v___x_5320_, v_o_5303_);
v___x_5322_ = lean_array_push(v___x_5321_, v_o_5306_);
v___x_5323_ = lean_array_push(v___x_5322_, v_a_5311_);
v___x_5324_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5315_, v___x_5316_, v___x_5323_, v___y_5224_);
lean_dec_ref(v___x_5323_);
return v___x_5324_;
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec(v_n_5307_);
lean_dec_ref(v_o_5306_);
lean_dec_ref(v_e_5305_);
lean_dec(v_n_5304_);
lean_dec_ref(v_o_5303_);
lean_dec_ref(v_e_5302_);
v_a_5325_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5310_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5310_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
else
{
uint8_t v___x_5333_; 
v___x_5333_ = lean_nat_dec_eq(v_n_5304_, v_n_5307_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5334_ = lean_nat_sub(v_n_5307_, v_n_5304_);
lean_dec(v_n_5304_);
lean_dec(v_n_5307_);
v___x_5335_ = l_Lean_mkNatLit(v___x_5334_);
lean_inc_ref(v_e_5305_);
v___x_5336_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5305_, v___x_5335_);
v___y_5134_ = v_e_5302_;
v___y_5135_ = v___y_5222_;
v___y_5136_ = v_e_5305_;
v___y_5137_ = v___y_5224_;
v___y_5138_ = v_o_5306_;
v___y_5139_ = v___y_5223_;
v___y_5140_ = v___y_5221_;
v___y_5141_ = v_o_5303_;
v___y_5142_ = v_leLvl_5220_;
v___y_5143_ = v___x_5336_;
goto v___jp_5133_;
}
else
{
lean_dec(v_n_5307_);
lean_dec(v_n_5304_);
lean_inc_ref(v_e_5305_);
v___y_5134_ = v_e_5302_;
v___y_5135_ = v___y_5222_;
v___y_5136_ = v_e_5305_;
v___y_5137_ = v___y_5224_;
v___y_5138_ = v_o_5306_;
v___y_5139_ = v___y_5223_;
v___y_5140_ = v___y_5221_;
v___y_5141_ = v_o_5303_;
v___y_5142_ = v_leLvl_5220_;
v___y_5143_ = v_e_5305_;
goto v___jp_5133_;
}
}
}
}
}
}
else
{
lean_object* v_a_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5347_; 
lean_del_object(v___x_5215_);
lean_dec(v_val_5213_);
lean_dec_ref(v___x_5179_);
lean_dec(v_val_5178_);
lean_dec_ref(v_p_5171_);
v_a_5340_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5342_ = v___x_5217_;
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_a_5340_);
lean_dec(v___x_5217_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5345_; 
if (v_isShared_5343_ == 0)
{
v___x_5345_ = v___x_5342_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
}
else
{
lean_object* v___x_5349_; lean_object* v___x_5351_; 
lean_dec(v_a_5209_);
lean_dec_ref(v___x_5179_);
lean_dec(v_val_5178_);
lean_dec_ref(v_p_5171_);
v___x_5349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 0, v___x_5349_);
v___x_5351_ = v___x_5211_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5349_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
lean_dec_ref(v___x_5179_);
lean_dec(v_val_5178_);
lean_dec_ref(v_p_5171_);
v_a_5354_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5208_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5208_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
v___jp_5180_:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; 
lean_inc_ref(v___x_5179_);
lean_inc_ref(v___y_5186_);
lean_inc(v___y_5187_);
v___x_5189_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_5187_, v___y_5186_, v___x_5179_);
v___x_5190_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5189_, v___y_5185_, v___y_5182_, v___y_5184_, v___y_5183_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___x_5190_, 1);
v___x_5192_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__3));
v___x_5193_ = lean_unsigned_to_nat(4u);
v___x_5194_ = lean_mk_empty_array_with_capacity(v___x_5193_);
v___x_5195_ = lean_array_push(v___x_5194_, v___y_5181_);
v___x_5196_ = lean_array_push(v___x_5195_, v___y_5186_);
v___x_5197_ = lean_array_push(v___x_5196_, v___x_5179_);
v___x_5198_ = lean_array_push(v___x_5197_, v_a_5191_);
v___x_5199_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___y_5188_, v___x_5192_, v___x_5198_, v___y_5183_);
lean_dec_ref(v___x_5198_);
return v___x_5199_;
}
else
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5207_; 
lean_dec_ref(v___y_5188_);
lean_dec_ref(v___y_5186_);
lean_dec_ref(v___y_5181_);
lean_dec_ref(v___x_5179_);
v_a_5200_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5202_ = v___x_5190_;
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5190_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5205_; 
if (v_isShared_5203_ == 0)
{
v___x_5205_ = v___x_5202_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
}
else
{
lean_object* v___x_5362_; lean_object* v___x_5364_; 
lean_dec(v_a_5174_);
lean_dec_ref(v_p_5171_);
v___x_5362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5177_ == 0)
{
lean_ctor_set(v___x_5176_, 0, v___x_5362_);
v___x_5364_ = v___x_5176_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5362_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec_ref(v_p_5171_);
v_a_5367_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5173_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5173_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
v___jp_5133_:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; 
lean_inc_ref(v___y_5138_);
lean_inc_ref(v___y_5141_);
lean_inc(v___y_5142_);
v___x_5144_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_5142_, v___y_5141_, v___y_5138_);
v___x_5145_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5144_, v___y_5140_, v___y_5135_, v___y_5139_, v___y_5137_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___x_5145_, 1);
lean_inc_ref(v___y_5134_);
v___x_5147_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___y_5134_, v___y_5143_);
v___x_5148_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__1));
v___x_5149_ = lean_unsigned_to_nat(5u);
v___x_5150_ = lean_mk_empty_array_with_capacity(v___x_5149_);
v___x_5151_ = lean_array_push(v___x_5150_, v___y_5134_);
v___x_5152_ = lean_array_push(v___x_5151_, v___y_5136_);
v___x_5153_ = lean_array_push(v___x_5152_, v___y_5141_);
v___x_5154_ = lean_array_push(v___x_5153_, v___y_5138_);
v___x_5155_ = lean_array_push(v___x_5154_, v_a_5146_);
v___x_5156_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_applySimprocConst___redArg(v___x_5147_, v___x_5148_, v___x_5155_, v___y_5137_);
lean_dec_ref(v___x_5155_);
return v___x_5156_;
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v___y_5143_);
lean_dec_ref(v___y_5141_);
lean_dec_ref(v___y_5138_);
lean_dec_ref(v___y_5136_);
lean_dec_ref(v___y_5134_);
v_a_5157_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5145_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5145_);
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
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object* v_e_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l_Nat_reduceSubDiff___redArg(v_e_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
lean_dec_ref(v_e_5375_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object* v_e_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l_Nat_reduceSubDiff___redArg(v_e_5382_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object* v_e_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Nat_reduceSubDiff(v_e_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
lean_dec(v_a_5393_);
lean_dec_ref(v_e_5392_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_));
v___x_5408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_));
v___x_5409_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5410_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5407_, v___x_5408_, v___x_5409_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26____boxed(lean_object* v_a_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_();
return v_res_5412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5413_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5413_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_5416_; uint8_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_));
v___x_5417_ = 1;
v___x_5418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_);
v___x_5419_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5416_, v___x_5417_, v___x_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28____boxed(lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_();
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_));
v___x_5424_ = 1;
v___x_5425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_);
v___x_5426_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5423_, v___x_5424_, v___x_5425_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_30____boxed(lean_object* v_a_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_30_();
return v_res_5428_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v___x_5438_ = lean_box(0);
v___x_5439_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__4));
v___x_5440_ = l_Lean_mkConst(v___x_5439_, v___x_5438_);
return v___x_5440_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5445_ = lean_box(0);
v___x_5446_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__7));
v___x_5447_ = l_Lean_mkConst(v___x_5446_, v___x_5445_);
return v___x_5447_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5452_ = lean_box(0);
v___x_5453_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__10));
v___x_5454_ = l_Lean_mkConst(v___x_5453_, v___x_5452_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object* v_e_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5455_, v_a_5457_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5582_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5464_ = v___x_5461_;
v_isShared_5465_ = v_isSharedCheck_5582_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5461_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5582_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5471_; uint8_t v___x_5472_; 
v___x_5471_ = l_Lean_Expr_cleanupAnnotations(v_a_5462_);
v___x_5472_ = l_Lean_Expr_isApp(v___x_5471_);
if (v___x_5472_ == 0)
{
lean_dec_ref(v___x_5471_);
goto v___jp_5466_;
}
else
{
lean_object* v_arg_5473_; lean_object* v___x_5474_; uint8_t v___x_5475_; 
v_arg_5473_ = lean_ctor_get(v___x_5471_, 1);
lean_inc_ref(v_arg_5473_);
v___x_5474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5471_);
v___x_5475_ = l_Lean_Expr_isApp(v___x_5474_);
if (v___x_5475_ == 0)
{
lean_dec_ref(v___x_5474_);
lean_dec_ref(v_arg_5473_);
goto v___jp_5466_;
}
else
{
lean_object* v_arg_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; 
v_arg_5476_ = lean_ctor_get(v___x_5474_, 1);
lean_inc_ref(v_arg_5476_);
v___x_5477_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5474_);
v___x_5478_ = l_Lean_Expr_isApp(v___x_5477_);
if (v___x_5478_ == 0)
{
lean_dec_ref(v___x_5477_);
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
goto v___jp_5466_;
}
else
{
lean_object* v_arg_5479_; lean_object* v___x_5480_; uint8_t v___x_5481_; 
v_arg_5479_ = lean_ctor_get(v___x_5477_, 1);
lean_inc_ref(v_arg_5479_);
v___x_5480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5477_);
v___x_5481_ = l_Lean_Expr_isApp(v___x_5480_);
if (v___x_5481_ == 0)
{
lean_dec_ref(v___x_5480_);
lean_dec_ref(v_arg_5479_);
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
goto v___jp_5466_;
}
else
{
lean_object* v___x_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; 
v___x_5482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5480_);
v___x_5483_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__2));
v___x_5484_ = l_Lean_Expr_isConstOf(v___x_5482_, v___x_5483_);
lean_dec_ref(v___x_5482_);
if (v___x_5484_ == 0)
{
lean_dec_ref(v_arg_5479_);
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
goto v___jp_5466_;
}
else
{
lean_object* v___x_5485_; lean_object* v___x_5486_; 
lean_del_object(v___x_5464_);
v___x_5485_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__5, &l_Nat_reduceDvd___redArg___closed__5_once, _init_l_Nat_reduceDvd___redArg___closed__5);
v___x_5486_ = l_Lean_Meta_matchesInstance(v_arg_5479_, v___x_5485_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5573_; 
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5573_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5573_ == 0)
{
v___x_5489_ = v___x_5486_;
v_isShared_5490_ = v_isSharedCheck_5573_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5486_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5573_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
uint8_t v___x_5491_; 
v___x_5491_ = lean_unbox(v_a_5487_);
lean_dec(v_a_5487_);
if (v___x_5491_ == 0)
{
lean_object* v___x_5492_; lean_object* v___x_5494_; 
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
v___x_5492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5490_ == 0)
{
lean_ctor_set(v___x_5489_, 0, v___x_5492_);
v___x_5494_ = v___x_5489_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
else
{
lean_object* v___x_5496_; 
lean_del_object(v___x_5489_);
v___x_5496_ = l_Lean_Meta_getNatValue_x3f(v_arg_5476_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5564_; 
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5499_ = v___x_5496_;
v_isShared_5500_ = v_isSharedCheck_5564_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5496_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5564_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
if (lean_obj_tag(v_a_5497_) == 1)
{
lean_object* v_val_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5559_; 
lean_del_object(v___x_5499_);
v_val_5501_ = lean_ctor_get(v_a_5497_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v_a_5497_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5503_ = v_a_5497_;
v_isShared_5504_ = v_isSharedCheck_5559_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_val_5501_);
lean_dec(v_a_5497_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5559_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v___x_5505_; 
v___x_5505_ = l_Lean_Meta_getNatValue_x3f(v_arg_5473_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5550_; 
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5508_ = v___x_5505_;
v_isShared_5509_ = v_isSharedCheck_5550_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5505_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5550_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
if (lean_obj_tag(v_a_5506_) == 1)
{
lean_object* v_val_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5545_; 
v_val_5510_ = lean_ctor_get(v_a_5506_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v_a_5506_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5512_ = v_a_5506_;
v_isShared_5513_ = v_isSharedCheck_5545_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_val_5510_);
lean_dec(v_a_5506_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5545_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; uint8_t v___x_5516_; 
v___x_5514_ = lean_nat_mod(v_val_5510_, v_val_5501_);
lean_dec(v_val_5501_);
lean_dec(v_val_5510_);
v___x_5515_ = lean_unsigned_to_nat(0u);
v___x_5516_ = lean_nat_dec_eq(v___x_5514_, v___x_5515_);
lean_dec(v___x_5514_);
if (v___x_5516_ == 0)
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5522_; 
v___x_5517_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_5518_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__8, &l_Nat_reduceDvd___redArg___closed__8_once, _init_l_Nat_reduceDvd___redArg___closed__8);
v___x_5519_ = l_Lean_eagerReflBoolTrue;
v___x_5520_ = l_Lean_mkApp3(v___x_5518_, v_arg_5476_, v_arg_5473_, v___x_5519_);
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 0, v___x_5520_);
v___x_5522_ = v___x_5512_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5520_);
v___x_5522_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5523_; lean_object* v___x_5525_; 
v___x_5523_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5523_, 0, v___x_5517_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*2, v___x_5484_);
if (v_isShared_5504_ == 0)
{
lean_ctor_set_tag(v___x_5503_, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5523_);
v___x_5525_ = v___x_5503_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5527_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 0, v___x_5525_);
v___x_5527_ = v___x_5508_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
else
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5536_; 
v___x_5531_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_5532_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__11, &l_Nat_reduceDvd___redArg___closed__11_once, _init_l_Nat_reduceDvd___redArg___closed__11);
v___x_5533_ = l_Lean_eagerReflBoolTrue;
v___x_5534_ = l_Lean_mkApp3(v___x_5532_, v_arg_5476_, v_arg_5473_, v___x_5533_);
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 0, v___x_5534_);
v___x_5536_ = v___x_5512_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5537_; lean_object* v___x_5539_; 
v___x_5537_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5537_, 0, v___x_5531_);
lean_ctor_set(v___x_5537_, 1, v___x_5536_);
lean_ctor_set_uint8(v___x_5537_, sizeof(void*)*2, v___x_5484_);
if (v_isShared_5504_ == 0)
{
lean_ctor_set_tag(v___x_5503_, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5537_);
v___x_5539_ = v___x_5503_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5541_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 0, v___x_5539_);
v___x_5541_ = v___x_5508_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
}
}
else
{
lean_object* v___x_5546_; lean_object* v___x_5548_; 
lean_dec(v_a_5506_);
lean_del_object(v___x_5503_);
lean_dec(v_val_5501_);
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
v___x_5546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 0, v___x_5546_);
v___x_5548_ = v___x_5508_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_del_object(v___x_5503_);
lean_dec(v_val_5501_);
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
v_a_5551_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5505_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5505_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
}
else
{
lean_object* v___x_5560_; lean_object* v___x_5562_; 
lean_dec(v_a_5497_);
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
v___x_5560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 0, v___x_5560_);
v___x_5562_ = v___x_5499_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5560_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
else
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5572_; 
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
v_a_5565_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5567_ = v___x_5496_;
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5496_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5570_; 
if (v_isShared_5568_ == 0)
{
v___x_5570_ = v___x_5567_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5565_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
}
}
else
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
lean_dec_ref(v_arg_5476_);
lean_dec_ref(v_arg_5473_);
v_a_5574_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5486_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5486_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
}
}
}
}
v___jp_5466_:
{
lean_object* v___x_5467_; lean_object* v___x_5469_; 
v___x_5467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 0, v___x_5467_);
v___x_5469_ = v___x_5464_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5467_);
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
else
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
v_a_5583_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v___x_5461_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5461_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg___boxed(lean_object* v_e_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_){
_start:
{
lean_object* v_res_5597_; 
v_res_5597_ = l_Nat_reduceDvd___redArg(v_e_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object* v_e_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_){
_start:
{
lean_object* v___x_5607_; 
v___x_5607_ = l_Nat_reduceDvd___redArg(v_e_5598_, v_a_5602_, v_a_5603_, v_a_5604_, v_a_5605_);
return v___x_5607_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object* v_e_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_){
_start:
{
lean_object* v_res_5617_; 
v_res_5617_ = l_Nat_reduceDvd(v_e_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_);
lean_dec(v_a_5615_);
lean_dec_ref(v_a_5614_);
lean_dec(v_a_5613_);
lean_dec_ref(v_a_5612_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
lean_dec(v_a_5609_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; 
v___x_5636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5638_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5639_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5636_, v___x_5637_, v___x_5638_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26____boxed(lean_object* v_a_5640_){
_start:
{
lean_object* v_res_5641_; 
v_res_5641_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_();
return v_res_5641_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_5642_; lean_object* v___x_5643_; 
v___x_5642_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_5645_; uint8_t v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5646_ = 1;
v___x_5647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_);
v___x_5648_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5645_, v___x_5646_, v___x_5647_);
return v___x_5648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28____boxed(lean_object* v_a_5649_){
_start:
{
lean_object* v_res_5650_; 
v_res_5650_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_();
return v_res_5650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_5652_; uint8_t v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
v___x_5652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_));
v___x_5653_ = 1;
v___x_5654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_28_);
v___x_5655_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5652_, v___x_5653_, v___x_5654_);
return v___x_5655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30____boxed(lean_object* v_a_5656_){
_start:
{
lean_object* v_res_5657_; 
v_res_5657_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_30_();
return v_res_5657_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OrderLevel(builtin);
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
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__29_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2577847471____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__34_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3409349834____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__39_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_121904536____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__44_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_746960771____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1952267129____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_395276852____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4206068689____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2089708235____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_994675004____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391429673____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3404948686____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_592671996____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__89_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3058597786____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__94_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351951051____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__99_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_30194753____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__104_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1404447611____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__109_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4243845176____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_993423656____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1391998651____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__178_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3606884043____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__186_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_351768507____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__191_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1369336426____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__196_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1622232758____hygCtx___hyg_26_();
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
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
