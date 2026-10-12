// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat import Lean.Util.SafeExponentiation import Init.Data.Int.DivMod
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_fmod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Int_fdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceNeg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Int_reduceNeg___redArg___closed__0 = (const lean_object*)&l_Int_reduceNeg___redArg___closed__0_value;
static const lean_string_object l_Int_reduceNeg___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Int_reduceNeg___redArg___closed__1 = (const lean_object*)&l_Int_reduceNeg___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceNeg___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceNeg___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Int_reduceNeg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNeg___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceNeg___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Int_reduceNeg___redArg___closed__2 = (const lean_object*)&l_Int_reduceNeg___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),LEAN_SCALAR_PTR_LITERAL(43, 197, 90, 191, 152, 17, 164, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isPosValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 255, 167, 193, 182, 39, 193)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceNeg___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reduceAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Int_reduceAdd___redArg___closed__0 = (const lean_object*)&l_Int_reduceAdd___redArg___closed__0_value;
static const lean_string_object l_Int_reduceAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Int_reduceAdd___redArg___closed__1 = (const lean_object*)&l_Int_reduceAdd___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceAdd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Int_reduceAdd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceAdd___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceAdd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Int_reduceAdd___redArg___closed__2 = (const lean_object*)&l_Int_reduceAdd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(199, 205, 212, 110, 180, 98, 113, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Int_reduceMul___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Int_reduceMul___redArg___closed__0 = (const lean_object*)&l_Int_reduceMul___redArg___closed__0_value;
static const lean_string_object l_Int_reduceMul___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Int_reduceMul___redArg___closed__1 = (const lean_object*)&l_Int_reduceMul___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceMul___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceMul___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Int_reduceMul___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceMul___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceMul___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Int_reduceMul___redArg___closed__2 = (const lean_object*)&l_Int_reduceMul___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(241, 202, 209, 45, 72, 65, 45, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Int_reduceSub___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Int_reduceSub___redArg___closed__0 = (const lean_object*)&l_Int_reduceSub___redArg___closed__0_value;
static const lean_string_object l_Int_reduceSub___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Int_reduceSub___redArg___closed__1 = (const lean_object*)&l_Int_reduceSub___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceSub___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceSub___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Int_reduceSub___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceSub___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceSub___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Int_reduceSub___redArg___closed__2 = (const lean_object*)&l_Int_reduceSub___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(13, 106, 226, 64, 164, 96, 43, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Int_reduceDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Int_reduceDiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceDiv___redArg___closed__0_value;
static const lean_string_object l_Int_reduceDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Int_reduceDiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceDiv___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceDiv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Int_reduceDiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDiv___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceDiv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Int_reduceDiv___redArg___closed__2 = (const lean_object*)&l_Int_reduceDiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(49, 255, 254, 198, 61, 74, 107, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Int_reduceMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Int_reduceMod___redArg___closed__0 = (const lean_object*)&l_Int_reduceMod___redArg___closed__0_value;
static const lean_string_object l_Int_reduceMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Int_reduceMod___redArg___closed__1 = (const lean_object*)&l_Int_reduceMod___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceMod___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Int_reduceMod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceMod___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceMod___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Int_reduceMod___redArg___closed__2 = (const lean_object*)&l_Int_reduceMod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(1, 71, 45, 195, 226, 201, 130, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l_Int_reduceTDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tdiv"};
static const lean_object* l_Int_reduceTDiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceTDiv___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceTDiv___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceTDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceTDiv___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceTDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 57, 32, 33, 207, 206, 80, 132)}};
static const lean_object* l_Int_reduceTDiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceTDiv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceTDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(5, 29, 196, 133, 149, 1, 127, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceTDiv___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reduceTMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tmod"};
static const lean_object* l_Int_reduceTMod___redArg___closed__0 = (const lean_object*)&l_Int_reduceTMod___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceTMod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceTMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceTMod___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceTMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 141, 33, 61, 13, 165, 12, 4)}};
static const lean_object* l_Int_reduceTMod___redArg___closed__1 = (const lean_object*)&l_Int_reduceTMod___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceTMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(175, 43, 120, 178, 42, 142, 112, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceTMod___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reduceFDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fdiv"};
static const lean_object* l_Int_reduceFDiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceFDiv___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceFDiv___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceFDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceFDiv___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceFDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 231, 68, 168, 157, 210, 86, 83)}};
static const lean_object* l_Int_reduceFDiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceFDiv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceFDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(53, 76, 90, 80, 250, 252, 49, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceFDiv___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reduceFMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fmod"};
static const lean_object* l_Int_reduceFMod___redArg___closed__0 = (const lean_object*)&l_Int_reduceFMod___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceFMod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceFMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceFMod___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceFMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 21, 173, 230, 223, 235, 156, 102)}};
static const lean_object* l_Int_reduceFMod___redArg___closed__1 = (const lean_object*)&l_Int_reduceFMod___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceFMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(196, 65, 95, 159, 113, 142, 76, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceFMod___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reduceBdiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bdiv"};
static const lean_object* l_Int_reduceBdiv___redArg___closed__0 = (const lean_object*)&l_Int_reduceBdiv___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceBdiv___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceBdiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBdiv___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceBdiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 137, 124, 202, 176, 195, 34, 196)}};
static const lean_object* l_Int_reduceBdiv___redArg___closed__1 = (const lean_object*)&l_Int_reduceBdiv___redArg___closed__1_value;
static const lean_closure_object l_Int_reduceBdiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_bdiv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_reduceBdiv___redArg___closed__2 = (const lean_object*)&l_Int_reduceBdiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBdiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(3, 226, 155, 73, 43, 47, 211, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBdiv___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reduceBmod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bmod"};
static const lean_object* l_Int_reduceBmod___redArg___closed__0 = (const lean_object*)&l_Int_reduceBmod___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceBmod___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceBmod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBmod___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceBmod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 85, 4, 38, 72, 77, 113, 148)}};
static const lean_object* l_Int_reduceBmod___redArg___closed__1 = (const lean_object*)&l_Int_reduceBmod___redArg___closed__1_value;
static const lean_closure_object l_Int_reduceBmod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_bmod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_reduceBmod___redArg___closed__2 = (const lean_object*)&l_Int_reduceBmod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBmod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(118, 7, 17, 12, 96, 102, 89, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBmod___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25____boxed(lean_object*);
static const lean_string_object l_Int_reducePow___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Int_reducePow___redArg___closed__0 = (const lean_object*)&l_Int_reducePow___redArg___closed__0_value;
static const lean_string_object l_Int_reducePow___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Int_reducePow___redArg___closed__1 = (const lean_object*)&l_Int_reducePow___redArg___closed__1_value;
static const lean_ctor_object l_Int_reducePow___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reducePow___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Int_reducePow___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reducePow___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reducePow___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Int_reducePow___redArg___closed__2 = (const lean_object*)&l_Int_reducePow___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducePow"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(50, 37, 139, 61, 189, 129, 123, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reducePow___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34____boxed(lean_object*);
static const lean_string_object l_Int_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Int_reduceLT___redArg___closed__0 = (const lean_object*)&l_Int_reduceLT___redArg___closed__0_value;
static const lean_string_object l_Int_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Int_reduceLT___redArg___closed__1 = (const lean_object*)&l_Int_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Int_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Int_reduceLT___redArg___closed__2 = (const lean_object*)&l_Int_reduceLT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(44, 74, 5, 214, 245, 132, 18, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Int_reduceLE___redArg___closed__0 = (const lean_object*)&l_Int_reduceLE___redArg___closed__0_value;
static const lean_string_object l_Int_reduceLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Int_reduceLE___redArg___closed__1 = (const lean_object*)&l_Int_reduceLE___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Int_reduceLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceLE___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceLE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Int_reduceLE___redArg___closed__2 = (const lean_object*)&l_Int_reduceLE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(162, 116, 1, 16, 180, 204, 211, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceGT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Int_reduceGT___redArg___closed__0 = (const lean_object*)&l_Int_reduceGT___redArg___closed__0_value;
static const lean_string_object l_Int_reduceGT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Int_reduceGT___redArg___closed__1 = (const lean_object*)&l_Int_reduceGT___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceGT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceGT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Int_reduceGT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceGT___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceGT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Int_reduceGT___redArg___closed__2 = (const lean_object*)&l_Int_reduceGT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(178, 9, 133, 164, 165, 111, 199, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceGE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Int_reduceGE___redArg___closed__0 = (const lean_object*)&l_Int_reduceGE___redArg___closed__0_value;
static const lean_string_object l_Int_reduceGE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Int_reduceGE___redArg___closed__1 = (const lean_object*)&l_Int_reduceGE___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceGE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceGE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Int_reduceGE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceGE___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceGE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Int_reduceGE___redArg___closed__2 = (const lean_object*)&l_Int_reduceGE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(23, 48, 177, 32, 118, 122, 123, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Int_reduceEq___redArg___closed__0 = (const lean_object*)&l_Int_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Int_reduceEq___redArg___closed__1 = (const lean_object*)&l_Int_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(245, 120, 38, 0, 146, 252, 195, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Int_reduceNe___redArg___closed__0 = (const lean_object*)&l_Int_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Int_reduceNe___redArg___closed__1 = (const lean_object*)&l_Int_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(110, 200, 224, 180, 186, 133, 131, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Int_reduceBEq___redArg___closed__0 = (const lean_object*)&l_Int_reduceBEq___redArg___closed__0_value;
static const lean_string_object l_Int_reduceBEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Int_reduceBEq___redArg___closed__1 = (const lean_object*)&l_Int_reduceBEq___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceBEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceBEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Int_reduceBEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceBEq___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceBEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Int_reduceBEq___redArg___closed__2 = (const lean_object*)&l_Int_reduceBEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 205, 147, 77, 92, 213, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Int_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Int_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Int_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Int_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Int_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(103, 51, 0, 45, 86, 105, 123, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceAbs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l_Int_reduceAbs___redArg___closed__0 = (const lean_object*)&l_Int_reduceAbs___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceAbs___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceAbs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceAbs___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceAbs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l_Int_reduceAbs___redArg___closed__1 = (const lean_object*)&l_Int_reduceAbs___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAbs"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(205, 160, 113, 110, 132, 211, 100, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceAbs___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceToNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Int_reduceToNat___redArg___closed__0 = (const lean_object*)&l_Int_reduceToNat___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceToNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceToNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceToNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceToNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 74, 209, 32, 95, 50, 220, 192)}};
static const lean_object* l_Int_reduceToNat___redArg___closed__1 = (const lean_object*)&l_Int_reduceToNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceToNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(54, 142, 202, 96, 211, 20, 233, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceToNat___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceNegSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Int_reduceNegSucc___redArg___closed__0 = (const lean_object*)&l_Int_reduceNegSucc___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceNegSucc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceNegSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNegSucc___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceNegSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Int_reduceNegSucc___redArg___closed__1 = (const lean_object*)&l_Int_reduceNegSucc___redArg___closed__1_value;
static lean_once_cell_t l_Int_reduceNegSucc___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceNegSucc___redArg___closed__2;
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceNegSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(93, 35, 228, 85, 244, 235, 146, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceNegSucc___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24____boxed(lean_object*);
static const lean_ctor_object l_Int_reduceOfNat___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceOfNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceOfNat___redArg___closed__0_value_aux_0),((lean_object*)&l_Int_reduceNeg___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Int_reduceOfNat___redArg___closed__0 = (const lean_object*)&l_Int_reduceOfNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(175, 50, 88, 129, 207, 23, 196, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceOfNat___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Int_reduceDvd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Int_reduceDvd___redArg___closed__0 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__0_value;
static const lean_string_object l_Int_reduceDvd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Int_reduceDvd___redArg___closed__1 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDvd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__2 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__2_value;
static const lean_string_object l_Int_reduceDvd___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Int_reduceDvd___redArg___closed__3 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__3_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__4_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__4 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__4_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__5;
static const lean_string_object l_Int_reduceDvd___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Int_reduceDvd___redArg___closed__6 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__6_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDvd___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__7 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__7_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__8;
static const lean_string_object l_Int_reduceDvd___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "dvd_eq_false_of_mod_ne_zero"};
static const lean_object* l_Int_reduceDvd___redArg___closed__9 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__9_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__10_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(115, 102, 95, 249, 149, 140, 145, 11)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__10 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__10_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__11;
static const lean_string_object l_Int_reduceDvd___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Int_reduceDvd___redArg___closed__12 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__12_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceDvd___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__13 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__13_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__14;
static const lean_string_object l_Int_reduceDvd___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "dvd_eq_true_of_mod_eq_zero"};
static const lean_object* l_Int_reduceDvd___redArg___closed__15 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__15_value;
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_reduceDvd___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__16_value_aux_0),((lean_object*)&l_Int_reduceDvd___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(249, 45, 36, 74, 66, 159, 93, 72)}};
static const lean_object* l_Int_reduceDvd___redArg___closed__16 = (const lean_object*)&l_Int_reduceDvd___redArg___closed__16_value;
static lean_once_cell_t l_Int_reduceDvd___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_reduceDvd___redArg___closed__17;
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value),LEAN_SCALAR_PTR_LITERAL(39, 115, 26, 72, 240, 81, 221, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceDvd___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_reduceNatCast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Int_reduceNatCast___redArg___closed__0 = (const lean_object*)&l_Int_reduceNatCast___redArg___closed__0_value;
static const lean_string_object l_Int_reduceNatCast___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Int_reduceNatCast___redArg___closed__1 = (const lean_object*)&l_Int_reduceNatCast___redArg___closed__1_value;
static const lean_ctor_object l_Int_reduceNatCast___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_reduceNatCast___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Int_reduceNatCast___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNatCast___redArg___closed__2_value_aux_0),((lean_object*)&l_Int_reduceNatCast___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Int_reduceNatCast___redArg___closed__2 = (const lean_object*)&l_Int_reduceNatCast___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceNatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(114, 75, 46, 148, 79, 192, 10, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Int_reduceNatCast___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27____boxed(lean_object*);
static const lean_string_object l_Int_reduceNatCast_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Int_reduceNatCast_x27___redArg___closed__0 = (const lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__0_value;
static const lean_ctor_object l_Int_reduceNatCast_x27___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Int_reduceNatCast_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__1_value_aux_0),((lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l_Int_reduceNatCast_x27___redArg___closed__1 = (const lean_object*)&l_Int_reduceNatCast_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceNatCast'"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(203, 3, 80, 245, 99, 222, 233, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27____boxed(lean_object*);
lean_object* l_Lean_Int_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getIntValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Lean_Int_fromExpr_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_Int_fromExpr_x3f___redArg(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___redArg___boxed(lean_object* v_e_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Int_fromExpr_x3f___redArg(v_e_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec_ref(v_a_12_);
lean_dec(v_a_11_);
lean_dec_ref(v_a_10_);
return v_res_15_;
}
}
lean_object* l_Lean_Int_fromExpr_x3f(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_getIntValue_x3f(v_e_16_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_Int_fromExpr_x3f_0interp(lean_interpreter_value* stack)
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
v_res_26_ = l_Lean_Int_fromExpr_x3f(v_e_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___boxed(lean_object* v_e_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Int_fromExpr_x3f(v_e_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_nat_to_int(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = l_Lean_Level_ofNat(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_box(0);
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5);
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6);
v___x_52_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4));
v___x_53_ = l_Lean_Expr_const___override(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9));
v___x_59_ = l_Lean_Expr_const___override(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12));
v___x_66_ = l_Lean_Expr_const___override(v___x_65_, v___x_64_);
return v___x_66_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg(lean_object* v_declName_67_, lean_object* v_arity_68_, lean_object* v_op_69_, lean_object* v_e_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_Expr_isAppOfArity(v_e_70_, v_declName_67_, v_arity_68_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec_ref(v_op_69_);
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = l_Lean_Expr_appArg_x21(v_e_70_);
v___x_80_ = l_Lean_Meta_getIntValue_x3f(v___x_79_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_106_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_106_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_106_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_106_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___y_86_; 
if (lean_obj_tag(v_a_81_) == 1)
{
lean_object* v_val_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_val_91_ = lean_ctor_get(v_a_81_, 0);
lean_inc(v_val_91_);
lean_dec_ref_known(v_a_81_, 1);
v___x_92_ = lean_apply_1(v_op_69_, v_val_91_);
v___x_93_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_94_ = lean_int_dec_le(v___x_93_, v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_95_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_96_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_98_ = lean_int_neg(v___x_92_);
lean_dec(v___x_92_);
v___x_99_ = l_Int_toNat(v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = l_Lean_instToExprInt_mkNat(v___x_99_);
v___x_101_ = l_Lean_mkApp3(v___x_95_, v___x_96_, v___x_97_, v___x_100_);
v___y_86_ = v___x_101_;
goto v___jp_85_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = l_Int_toNat(v___x_92_);
lean_dec(v___x_92_);
v___x_103_ = l_Lean_instToExprInt_mkNat(v___x_102_);
v___y_86_ = v___x_103_;
goto v___jp_85_;
}
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_del_object(v___x_83_);
lean_dec(v_a_81_);
lean_dec_ref(v_op_69_);
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___y_86_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_87_);
v___x_89_ = v___x_83_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec_ref(v_op_69_);
v_a_107_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_80_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_80_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_67_ = stack[0].m_obj;
lean_object* v_arity_68_ = stack[1].m_obj;
lean_object* v_op_69_ = stack[2].m_obj;
lean_object* v_e_70_ = stack[3].m_obj;
lean_object* v_a_71_ = stack[4].m_obj;
lean_object* v_a_72_ = stack[5].m_obj;
lean_object* v_a_73_ = stack[6].m_obj;
lean_object* v_a_74_ = stack[7].m_obj;
lean_object* v_res_115_;
v_res_115_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg(v_declName_67_, v_arity_68_, v_op_69_, v_e_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___boxed(lean_object* v_declName_116_, lean_object* v_arity_117_, lean_object* v_op_118_, lean_object* v_e_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg(v_declName_116_, v_arity_117_, v_op_118_, v_e_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec_ref(v_e_119_);
lean_dec(v_declName_116_);
return v_res_125_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary(lean_object* v_declName_126_, lean_object* v_arity_127_, lean_object* v_op_128_, lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Lean_Expr_isAppOfArity(v_e_129_, v_declName_126_, v_arity_127_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec_ref(v_op_128_);
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Lean_Expr_appArg_x21(v_e_129_);
v___x_142_ = l_Lean_Meta_getIntValue_x3f(v___x_141_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_168_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_168_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_168_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_168_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___y_148_; 
if (lean_obj_tag(v_a_143_) == 1)
{
lean_object* v_val_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_val_153_ = lean_ctor_get(v_a_143_, 0);
lean_inc(v_val_153_);
lean_dec_ref_known(v_a_143_, 1);
v___x_154_ = lean_apply_1(v_op_128_, v_val_153_);
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_156_ = lean_int_dec_le(v___x_155_, v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_160_ = lean_int_neg(v___x_154_);
lean_dec(v___x_154_);
v___x_161_ = l_Int_toNat(v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = l_Lean_instToExprInt_mkNat(v___x_161_);
v___x_163_ = l_Lean_mkApp3(v___x_157_, v___x_158_, v___x_159_, v___x_162_);
v___y_148_ = v___x_163_;
goto v___jp_147_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = l_Int_toNat(v___x_154_);
lean_dec(v___x_154_);
v___x_165_ = l_Lean_instToExprInt_mkNat(v___x_164_);
v___y_148_ = v___x_165_;
goto v___jp_147_;
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_del_object(v___x_145_);
lean_dec(v_a_143_);
lean_dec_ref(v_op_128_);
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___y_148_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_149_);
v___x_151_ = v___x_145_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec_ref(v_op_128_);
v_a_169_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_142_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_142_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_126_ = stack[0].m_obj;
lean_object* v_arity_127_ = stack[1].m_obj;
lean_object* v_op_128_ = stack[2].m_obj;
lean_object* v_e_129_ = stack[3].m_obj;
lean_object* v_a_130_ = stack[4].m_obj;
lean_object* v_a_131_ = stack[5].m_obj;
lean_object* v_a_132_ = stack[6].m_obj;
lean_object* v_a_133_ = stack[7].m_obj;
lean_object* v_a_134_ = stack[8].m_obj;
lean_object* v_a_135_ = stack[9].m_obj;
lean_object* v_a_136_ = stack[10].m_obj;
lean_object* v_res_177_;
v_res_177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary(v_declName_126_, v_arity_127_, v_op_128_, v_e_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___boxed(lean_object* v_declName_178_, lean_object* v_arity_179_, lean_object* v_op_180_, lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary(v_declName_178_, v_arity_179_, v_op_180_, v_e_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_e_181_);
lean_dec(v_declName_178_);
return v_res_190_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg(lean_object* v_declName_191_, lean_object* v_arity_192_, lean_object* v_op_193_, lean_object* v_e_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_Expr_isAppOfArity(v_e_194_, v_declName_191_, v_arity_192_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_op_193_);
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = l_Lean_Expr_appFn_x21(v_e_194_);
v___x_204_ = l_Lean_Expr_appArg_x21(v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = l_Lean_Meta_getIntValue_x3f(v___x_204_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_259_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_259_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_259_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_259_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
if (lean_obj_tag(v_a_206_) == 1)
{
lean_object* v_val_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_254_; 
v_val_210_ = lean_ctor_get(v_a_206_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_254_ == 0)
{
v___x_212_ = v_a_206_;
v_isShared_213_ = v_isSharedCheck_254_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_val_210_);
lean_dec(v_a_206_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_254_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = l_Lean_Expr_appArg_x21(v_e_194_);
v___x_215_ = l_Lean_Meta_getIntValue_x3f(v___x_214_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_245_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_245_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_245_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_245_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___y_221_; 
if (lean_obj_tag(v_a_216_) == 1)
{
lean_object* v_val_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
lean_del_object(v___x_208_);
v_val_228_ = lean_ctor_get(v_a_216_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v_a_216_, 1);
v___x_229_ = lean_apply_2(v_op_193_, v_val_210_, v_val_228_);
v___x_230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_231_ = lean_int_dec_le(v___x_230_, v___x_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_235_ = lean_int_neg(v___x_229_);
lean_dec(v___x_229_);
v___x_236_ = l_Int_toNat(v___x_235_);
lean_dec(v___x_235_);
v___x_237_ = l_Lean_instToExprInt_mkNat(v___x_236_);
v___x_238_ = l_Lean_mkApp3(v___x_232_, v___x_233_, v___x_234_, v___x_237_);
v___y_221_ = v___x_238_;
goto v___jp_220_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = l_Int_toNat(v___x_229_);
lean_dec(v___x_229_);
v___x_240_ = l_Lean_instToExprInt_mkNat(v___x_239_);
v___y_221_ = v___x_240_;
goto v___jp_220_;
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_243_; 
lean_del_object(v___x_218_);
lean_dec(v_a_216_);
lean_del_object(v___x_212_);
lean_dec(v_val_210_);
lean_dec_ref(v_op_193_);
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_241_);
v___x_243_ = v___x_208_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
v___jp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 0);
lean_ctor_set(v___x_212_, 0, v___y_221_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___y_221_);
v___x_223_ = v_reuseFailAlloc_227_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_223_);
v___x_225_ = v___x_218_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_del_object(v___x_212_);
lean_dec(v_val_210_);
lean_del_object(v___x_208_);
lean_dec_ref(v_op_193_);
v_a_246_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_215_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_215_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec(v_a_206_);
lean_dec_ref(v_op_193_);
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_255_);
v___x_257_ = v___x_208_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_op_193_);
v_a_260_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_205_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_205_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_191_ = stack[0].m_obj;
lean_object* v_arity_192_ = stack[1].m_obj;
lean_object* v_op_193_ = stack[2].m_obj;
lean_object* v_e_194_ = stack[3].m_obj;
lean_object* v_a_195_ = stack[4].m_obj;
lean_object* v_a_196_ = stack[5].m_obj;
lean_object* v_a_197_ = stack[6].m_obj;
lean_object* v_a_198_ = stack[7].m_obj;
lean_object* v_res_268_;
v_res_268_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg(v_declName_191_, v_arity_192_, v_op_193_, v_e_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg___boxed(lean_object* v_declName_269_, lean_object* v_arity_270_, lean_object* v_op_271_, lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg(v_declName_269_, v_arity_270_, v_op_271_, v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec_ref(v_e_272_);
lean_dec(v_declName_269_);
return v_res_278_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin(lean_object* v_declName_279_, lean_object* v_arity_280_, lean_object* v_op_281_, lean_object* v_e_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Lean_Expr_isAppOfArity(v_e_282_, v_declName_279_, v_arity_280_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref(v_op_281_);
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = l_Lean_Expr_appFn_x21(v_e_282_);
v___x_295_ = l_Lean_Expr_appArg_x21(v___x_294_);
lean_dec_ref(v___x_294_);
v___x_296_ = l_Lean_Meta_getIntValue_x3f(v___x_295_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_350_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_350_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_350_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_350_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
if (lean_obj_tag(v_a_297_) == 1)
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_345_; 
v_val_301_ = lean_ctor_get(v_a_297_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_297_);
if (v_isSharedCheck_345_ == 0)
{
v___x_303_ = v_a_297_;
v_isShared_304_ = v_isSharedCheck_345_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v_a_297_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_345_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l_Lean_Expr_appArg_x21(v_e_282_);
v___x_306_ = l_Lean_Meta_getIntValue_x3f(v___x_305_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_336_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_336_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_336_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_336_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___y_312_; 
if (lean_obj_tag(v_a_307_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
lean_del_object(v___x_299_);
v_val_319_ = lean_ctor_get(v_a_307_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v_a_307_, 1);
v___x_320_ = lean_apply_2(v_op_281_, v_val_301_, v_val_319_);
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_322_ = lean_int_dec_le(v___x_321_, v___x_320_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_326_ = lean_int_neg(v___x_320_);
lean_dec(v___x_320_);
v___x_327_ = l_Int_toNat(v___x_326_);
lean_dec(v___x_326_);
v___x_328_ = l_Lean_instToExprInt_mkNat(v___x_327_);
v___x_329_ = l_Lean_mkApp3(v___x_323_, v___x_324_, v___x_325_, v___x_328_);
v___y_312_ = v___x_329_;
goto v___jp_311_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = l_Int_toNat(v___x_320_);
lean_dec(v___x_320_);
v___x_331_ = l_Lean_instToExprInt_mkNat(v___x_330_);
v___y_312_ = v___x_331_;
goto v___jp_311_;
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_334_; 
lean_del_object(v___x_309_);
lean_dec(v_a_307_);
lean_del_object(v___x_303_);
lean_dec(v_val_301_);
lean_dec_ref(v_op_281_);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_332_);
v___x_334_ = v___x_299_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
v___jp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 0);
lean_ctor_set(v___x_303_, 0, v___y_312_);
v___x_314_ = v___x_303_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___y_312_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_314_);
v___x_316_ = v___x_309_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_del_object(v___x_303_);
lean_dec(v_val_301_);
lean_del_object(v___x_299_);
lean_dec_ref(v_op_281_);
v_a_337_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_306_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_306_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec(v_a_297_);
lean_dec_ref(v_op_281_);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_346_);
v___x_348_ = v___x_299_;
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
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_op_281_);
v_a_351_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_296_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_296_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_279_ = stack[0].m_obj;
lean_object* v_arity_280_ = stack[1].m_obj;
lean_object* v_op_281_ = stack[2].m_obj;
lean_object* v_e_282_ = stack[3].m_obj;
lean_object* v_a_283_ = stack[4].m_obj;
lean_object* v_a_284_ = stack[5].m_obj;
lean_object* v_a_285_ = stack[6].m_obj;
lean_object* v_a_286_ = stack[7].m_obj;
lean_object* v_a_287_ = stack[8].m_obj;
lean_object* v_a_288_ = stack[9].m_obj;
lean_object* v_a_289_ = stack[10].m_obj;
lean_object* v_res_359_;
v_res_359_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin(v_declName_279_, v_arity_280_, v_op_281_, v_e_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___boxed(lean_object* v_declName_360_, lean_object* v_arity_361_, lean_object* v_op_362_, lean_object* v_e_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin(v_declName_360_, v_arity_361_, v_op_362_, v_e_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_e_363_);
lean_dec(v_declName_360_);
return v_res_372_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(lean_object* v_name_373_, lean_object* v_op_374_, lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(2u);
v___x_382_ = l_Lean_Expr_isAppOfArity(v_e_375_, v_name_373_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec_ref(v_op_374_);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_Expr_appFn_x21(v_e_375_);
v___x_386_ = l_Lean_Expr_appArg_x21(v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = l_Lean_Meta_getIntValue_x3f(v___x_386_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_441_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_441_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_441_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_441_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
if (lean_obj_tag(v_a_388_) == 1)
{
lean_object* v_val_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_436_; 
v_val_392_ = lean_ctor_get(v_a_388_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_a_388_);
if (v_isSharedCheck_436_ == 0)
{
v___x_394_ = v_a_388_;
v_isShared_395_ = v_isSharedCheck_436_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_val_392_);
lean_dec(v_a_388_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_436_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l_Lean_Expr_appArg_x21(v_e_375_);
v___x_397_ = l_Lean_Meta_getNatValue_x3f(v___x_396_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec_ref(v___x_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_427_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_427_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_427_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_427_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___y_403_; 
if (lean_obj_tag(v_a_398_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
lean_del_object(v___x_390_);
v_val_410_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_a_398_, 1);
v___x_411_ = lean_apply_2(v_op_374_, v_val_392_, v_val_410_);
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_413_ = lean_int_dec_le(v___x_412_, v___x_411_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_417_ = lean_int_neg(v___x_411_);
lean_dec(v___x_411_);
v___x_418_ = l_Int_toNat(v___x_417_);
lean_dec(v___x_417_);
v___x_419_ = l_Lean_instToExprInt_mkNat(v___x_418_);
v___x_420_ = l_Lean_mkApp3(v___x_414_, v___x_415_, v___x_416_, v___x_419_);
v___y_403_ = v___x_420_;
goto v___jp_402_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = l_Int_toNat(v___x_411_);
lean_dec(v___x_411_);
v___x_422_ = l_Lean_instToExprInt_mkNat(v___x_421_);
v___y_403_ = v___x_422_;
goto v___jp_402_;
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_425_; 
lean_del_object(v___x_400_);
lean_dec(v_a_398_);
lean_del_object(v___x_394_);
lean_dec(v_val_392_);
lean_dec_ref(v_op_374_);
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_423_);
v___x_425_ = v___x_390_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
v___jp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 0);
lean_ctor_set(v___x_394_, 0, v___y_403_);
v___x_405_ = v___x_394_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___y_403_);
v___x_405_ = v_reuseFailAlloc_409_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_405_);
v___x_407_ = v___x_400_;
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
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_del_object(v___x_394_);
lean_dec(v_val_392_);
lean_del_object(v___x_390_);
lean_dec_ref(v_op_374_);
v_a_428_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_397_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_397_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_439_; 
lean_dec(v_a_388_);
lean_dec_ref(v_op_374_);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_437_);
v___x_439_ = v___x_390_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_op_374_);
v_a_442_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_387_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_387_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_373_ = stack[0].m_obj;
lean_object* v_op_374_ = stack[1].m_obj;
lean_object* v_e_375_ = stack[2].m_obj;
lean_object* v_a_376_ = stack[3].m_obj;
lean_object* v_a_377_ = stack[4].m_obj;
lean_object* v_a_378_ = stack[5].m_obj;
lean_object* v_a_379_ = stack[6].m_obj;
lean_object* v_res_450_;
v_res_450_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v_name_373_, v_op_374_, v_e_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg___boxed(lean_object* v_name_451_, lean_object* v_op_452_, lean_object* v_e_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v_name_451_, v_op_452_, v_e_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_e_453_);
lean_dec(v_name_451_);
return v_res_459_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp(lean_object* v_name_460_, lean_object* v_op_461_, lean_object* v_e_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v_name_460_, v_op_461_, v_e_462_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
return v___x_471_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_460_ = stack[0].m_obj;
lean_object* v_op_461_ = stack[1].m_obj;
lean_object* v_e_462_ = stack[2].m_obj;
lean_object* v_a_463_ = stack[3].m_obj;
lean_object* v_a_464_ = stack[4].m_obj;
lean_object* v_a_465_ = stack[5].m_obj;
lean_object* v_a_466_ = stack[6].m_obj;
lean_object* v_a_467_ = stack[7].m_obj;
lean_object* v_a_468_ = stack[8].m_obj;
lean_object* v_a_469_ = stack[9].m_obj;
lean_object* v_res_472_;
v_res_472_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp(v_name_460_, v_op_461_, v_e_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___boxed(lean_object* v_name_473_, lean_object* v_op_474_, lean_object* v_e_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp(v_name_473_, v_op_474_, v_e_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_e_475_);
lean_dec(v_name_473_);
return v_res_484_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg(lean_object* v_declName_487_, lean_object* v_arity_488_, lean_object* v_op_489_, lean_object* v_e_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = l_Lean_Expr_isAppOfArity(v_e_490_, v_declName_487_, v_arity_488_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref(v_e_490_);
lean_dec_ref(v_op_489_);
v___x_497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = l_Lean_Expr_appFn_x21(v_e_490_);
v___x_500_ = l_Lean_Expr_appArg_x21(v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = l_Lean_Meta_getIntValue_x3f(v___x_500_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_534_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_534_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_534_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_534_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
if (lean_obj_tag(v_a_502_) == 1)
{
lean_object* v_val_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_del_object(v___x_504_);
v_val_506_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_502_, 1);
v___x_507_ = l_Lean_Expr_appArg_x21(v_e_490_);
v___x_508_ = l_Lean_Meta_getIntValue_x3f(v___x_507_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_521_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_521_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
if (lean_obj_tag(v_a_509_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
lean_del_object(v___x_511_);
v_val_513_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_a_509_, 1);
v___x_514_ = lean_apply_2(v_op_489_, v_val_506_, v_val_513_);
v___x_515_ = lean_unbox(v___x_514_);
v___x_516_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_490_, v___x_515_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec(v_a_509_);
lean_dec(v_val_506_);
lean_dec_ref(v_e_490_);
lean_dec_ref(v_op_489_);
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_517_);
v___x_519_ = v___x_511_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_val_506_);
lean_dec_ref(v_e_490_);
lean_dec_ref(v_op_489_);
v_a_522_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_508_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_508_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_532_; 
lean_dec(v_a_502_);
lean_dec_ref(v_e_490_);
lean_dec_ref(v_op_489_);
v___x_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_530_);
v___x_532_ = v___x_504_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_e_490_);
lean_dec_ref(v_op_489_);
v_a_535_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_501_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_501_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_487_ = stack[0].m_obj;
lean_object* v_arity_488_ = stack[1].m_obj;
lean_object* v_op_489_ = stack[2].m_obj;
lean_object* v_e_490_ = stack[3].m_obj;
lean_object* v_a_491_ = stack[4].m_obj;
lean_object* v_a_492_ = stack[5].m_obj;
lean_object* v_a_493_ = stack[6].m_obj;
lean_object* v_a_494_ = stack[7].m_obj;
lean_object* v_res_543_;
v_res_543_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg(v_declName_487_, v_arity_488_, v_op_489_, v_e_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___boxed(lean_object* v_declName_544_, lean_object* v_arity_545_, lean_object* v_op_546_, lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg(v_declName_544_, v_arity_545_, v_op_546_, v_e_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_declName_544_);
return v_res_553_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred(lean_object* v_declName_554_, lean_object* v_arity_555_, lean_object* v_op_556_, lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = l_Lean_Expr_isAppOfArity(v_e_557_, v_declName_554_, v_arity_555_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v_e_557_);
lean_dec_ref(v_op_556_);
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = l_Lean_Expr_appFn_x21(v_e_557_);
v___x_570_ = l_Lean_Expr_appArg_x21(v___x_569_);
lean_dec_ref(v___x_569_);
v___x_571_ = l_Lean_Meta_getIntValue_x3f(v___x_570_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_604_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_604_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_604_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_604_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_a_572_) == 1)
{
lean_object* v_val_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_del_object(v___x_574_);
v_val_576_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v_a_572_, 1);
v___x_577_ = l_Lean_Expr_appArg_x21(v_e_557_);
v___x_578_ = l_Lean_Meta_getIntValue_x3f(v___x_577_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_591_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_591_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
if (lean_obj_tag(v_a_579_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
lean_del_object(v___x_581_);
v_val_583_ = lean_ctor_get(v_a_579_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_a_579_, 1);
v___x_584_ = lean_apply_2(v_op_556_, v_val_576_, v_val_583_);
v___x_585_ = lean_unbox(v___x_584_);
v___x_586_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_557_, v___x_585_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_dec(v_a_579_);
lean_dec(v_val_576_);
lean_dec_ref(v_e_557_);
lean_dec_ref(v_op_556_);
v___x_587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_587_);
v___x_589_ = v___x_581_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_val_576_);
lean_dec_ref(v_e_557_);
lean_dec_ref(v_op_556_);
v_a_592_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_578_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_578_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec(v_a_572_);
lean_dec_ref(v_e_557_);
lean_dec_ref(v_op_556_);
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_600_);
v___x_602_ = v___x_574_;
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
lean_dec_ref(v_e_557_);
lean_dec_ref(v_op_556_);
v_a_605_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_571_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_571_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_554_ = stack[0].m_obj;
lean_object* v_arity_555_ = stack[1].m_obj;
lean_object* v_op_556_ = stack[2].m_obj;
lean_object* v_e_557_ = stack[3].m_obj;
lean_object* v_a_558_ = stack[4].m_obj;
lean_object* v_a_559_ = stack[5].m_obj;
lean_object* v_a_560_ = stack[6].m_obj;
lean_object* v_a_561_ = stack[7].m_obj;
lean_object* v_a_562_ = stack[8].m_obj;
lean_object* v_a_563_ = stack[9].m_obj;
lean_object* v_a_564_ = stack[10].m_obj;
lean_object* v_res_613_;
v_res_613_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred(v_declName_554_, v_arity_555_, v_op_556_, v_e_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___boxed(lean_object* v_declName_614_, lean_object* v_arity_615_, lean_object* v_op_616_, lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred(v_declName_614_, v_arity_615_, v_op_616_, v_e_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec(v_declName_614_);
return v_res_626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_box(0);
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2));
v___x_634_ = l_Lean_mkConst(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_box(0);
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5));
v___x_641_ = l_Lean_mkConst(v___x_640_, v___x_639_);
return v___x_641_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg(lean_object* v_declName_642_, lean_object* v_arity_643_, lean_object* v_op_644_, lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_isAppOfArity(v_e_645_, v_declName_642_, v_arity_643_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v_op_644_);
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = l_Lean_Expr_appFn_x21(v_e_645_);
v___x_655_ = l_Lean_Expr_appArg_x21(v___x_654_);
lean_dec_ref(v___x_654_);
v___x_656_ = l_Lean_Meta_getIntValue_x3f(v___x_655_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_702_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_702_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_702_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_702_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
if (lean_obj_tag(v_a_657_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_697_; 
v_val_661_ = lean_ctor_get(v_a_657_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_697_ == 0)
{
v___x_663_ = v_a_657_;
v_isShared_664_ = v_isSharedCheck_697_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v_a_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_697_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Lean_Expr_appArg_x21(v_e_645_);
v___x_666_ = l_Lean_Meta_getIntValue_x3f(v___x_665_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_688_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_688_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_688_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_688_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___y_672_; 
if (lean_obj_tag(v_a_667_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
lean_del_object(v___x_659_);
v_val_679_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_a_667_, 1);
v___x_680_ = lean_apply_2(v_op_644_, v_val_661_, v_val_679_);
v___x_681_ = lean_unbox(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_672_ = v___x_682_;
goto v___jp_671_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_672_ = v___x_683_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_del_object(v___x_669_);
lean_dec(v_a_667_);
lean_del_object(v___x_663_);
lean_dec(v_val_661_);
lean_dec_ref(v_op_644_);
v___x_684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_684_);
v___x_686_ = v___x_659_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
v___jp_671_:
{
lean_object* v___x_674_; 
lean_inc_ref(v___y_672_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 0);
lean_ctor_set(v___x_663_, 0, v___y_672_);
v___x_674_ = v___x_663_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___y_672_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_674_);
v___x_676_ = v___x_669_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_del_object(v___x_663_);
lean_dec(v_val_661_);
lean_del_object(v___x_659_);
lean_dec_ref(v_op_644_);
v_a_689_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_666_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_666_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_700_; 
lean_dec(v_a_657_);
lean_dec_ref(v_op_644_);
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_698_);
v___x_700_ = v___x_659_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_op_644_);
v_a_703_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_656_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_656_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_642_ = stack[0].m_obj;
lean_object* v_arity_643_ = stack[1].m_obj;
lean_object* v_op_644_ = stack[2].m_obj;
lean_object* v_e_645_ = stack[3].m_obj;
lean_object* v_a_646_ = stack[4].m_obj;
lean_object* v_a_647_ = stack[5].m_obj;
lean_object* v_a_648_ = stack[6].m_obj;
lean_object* v_a_649_ = stack[7].m_obj;
lean_object* v_res_711_;
v_res_711_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg(v_declName_642_, v_arity_643_, v_op_644_, v_e_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___boxed(lean_object* v_declName_712_, lean_object* v_arity_713_, lean_object* v_op_714_, lean_object* v_e_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg(v_declName_712_, v_arity_713_, v_op_714_, v_e_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec_ref(v_e_715_);
lean_dec(v_declName_712_);
return v_res_721_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred(lean_object* v_declName_722_, lean_object* v_arity_723_, lean_object* v_op_724_, lean_object* v_e_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = l_Lean_Expr_isAppOfArity(v_e_725_, v_declName_722_, v_arity_723_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref(v_op_724_);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_Expr_appFn_x21(v_e_725_);
v___x_738_ = l_Lean_Expr_appArg_x21(v___x_737_);
lean_dec_ref(v___x_737_);
v___x_739_ = l_Lean_Meta_getIntValue_x3f(v___x_738_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_785_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_785_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_785_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_785_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
if (lean_obj_tag(v_a_740_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_780_; 
v_val_744_ = lean_ctor_get(v_a_740_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_780_ == 0)
{
v___x_746_ = v_a_740_;
v_isShared_747_ = v_isSharedCheck_780_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_val_744_);
lean_dec(v_a_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_780_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Lean_Expr_appArg_x21(v_e_725_);
v___x_749_ = l_Lean_Meta_getIntValue_x3f(v___x_748_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_771_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_771_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_771_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_771_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___y_755_; 
if (lean_obj_tag(v_a_750_) == 1)
{
lean_object* v_val_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
lean_del_object(v___x_742_);
v_val_762_ = lean_ctor_get(v_a_750_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_a_750_, 1);
v___x_763_ = lean_apply_2(v_op_724_, v_val_744_, v_val_762_);
v___x_764_ = lean_unbox(v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_755_ = v___x_765_;
goto v___jp_754_;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_755_ = v___x_766_;
goto v___jp_754_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_del_object(v___x_752_);
lean_dec(v_a_750_);
lean_del_object(v___x_746_);
lean_dec(v_val_744_);
lean_dec_ref(v_op_724_);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_767_);
v___x_769_ = v___x_742_;
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
v___jp_754_:
{
lean_object* v___x_757_; 
lean_inc_ref(v___y_755_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 0);
lean_ctor_set(v___x_746_, 0, v___y_755_);
v___x_757_ = v___x_746_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___y_755_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_757_);
v___x_759_ = v___x_752_;
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
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_del_object(v___x_746_);
lean_dec(v_val_744_);
lean_del_object(v___x_742_);
lean_dec_ref(v_op_724_);
v_a_772_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_749_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_749_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_a_740_);
lean_dec_ref(v_op_724_);
v___x_781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_781_);
v___x_783_ = v___x_742_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
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
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_op_724_);
v_a_786_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_739_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_739_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_722_ = stack[0].m_obj;
lean_object* v_arity_723_ = stack[1].m_obj;
lean_object* v_op_724_ = stack[2].m_obj;
lean_object* v_e_725_ = stack[3].m_obj;
lean_object* v_a_726_ = stack[4].m_obj;
lean_object* v_a_727_ = stack[5].m_obj;
lean_object* v_a_728_ = stack[6].m_obj;
lean_object* v_a_729_ = stack[7].m_obj;
lean_object* v_a_730_ = stack[8].m_obj;
lean_object* v_a_731_ = stack[9].m_obj;
lean_object* v_a_732_ = stack[10].m_obj;
lean_object* v_res_794_;
v_res_794_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred(v_declName_722_, v_arity_723_, v_op_724_, v_e_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___boxed(lean_object* v_declName_795_, lean_object* v_arity_796_, lean_object* v_op_797_, lean_object* v_e_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred(v_declName_795_, v_arity_796_, v_op_797_, v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_e_798_);
lean_dec(v_declName_795_);
return v_res_807_;
}
}
lean_object* l_Int_reduceNeg___redArg(lean_object* v_e_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___y_826_; lean_object* v___x_829_; 
lean_inc_ref(v_e_813_);
v___x_829_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_813_, v_a_815_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = l_Lean_Expr_cleanupAnnotations(v_a_830_);
v___x_832_ = l_Lean_Expr_isApp(v___x_831_);
if (v___x_832_ == 0)
{
lean_dec_ref(v___x_831_);
lean_dec_ref(v_e_813_);
goto v___jp_822_;
}
else
{
lean_object* v_arg_833_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_arg_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc_ref(v_arg_833_);
v___x_870_ = l_Lean_Expr_appFnCleanup___redArg(v___x_831_);
v___x_871_ = l_Lean_Expr_isApp(v___x_870_);
if (v___x_871_ == 0)
{
lean_dec_ref(v___x_870_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_e_813_);
goto v___jp_822_;
}
else
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = l_Lean_Expr_appFnCleanup___redArg(v___x_870_);
v___x_873_ = l_Lean_Expr_isApp(v___x_872_);
if (v___x_873_ == 0)
{
lean_dec_ref(v___x_872_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_e_813_);
goto v___jp_822_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_872_);
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4));
v___x_876_ = l_Lean_Expr_isConstOf(v___x_874_, v___x_875_);
lean_dec_ref(v___x_874_);
if (v___x_876_ == 0)
{
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_e_813_);
goto v___jp_822_;
}
else
{
lean_object* v___x_877_; 
lean_inc_ref(v_arg_833_);
v___x_877_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_833_, v_a_815_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_906_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_906_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_906_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_906_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = l_Lean_Expr_cleanupAnnotations(v_a_878_);
v___x_883_ = l_Lean_Expr_isApp(v___x_882_);
if (v___x_883_ == 0)
{
lean_dec_ref(v___x_882_);
lean_del_object(v___x_880_);
lean_dec_ref(v_e_813_);
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
goto v___jp_834_;
}
else
{
lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_884_ = l_Lean_Expr_appFnCleanup___redArg(v___x_882_);
v___x_885_ = l_Lean_Expr_isApp(v___x_884_);
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_884_);
lean_del_object(v___x_880_);
lean_dec_ref(v_e_813_);
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
goto v___jp_834_;
}
else
{
lean_object* v_arg_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_arg_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc_ref(v_arg_886_);
v___x_887_ = l_Lean_Expr_appFnCleanup___redArg(v___x_884_);
v___x_888_ = l_Lean_Expr_isApp(v___x_887_);
if (v___x_888_ == 0)
{
lean_dec_ref(v___x_887_);
lean_dec_ref(v_arg_886_);
lean_del_object(v___x_880_);
lean_dec_ref(v_e_813_);
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
goto v___jp_834_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_889_ = l_Lean_Expr_appFnCleanup___redArg(v___x_887_);
v___x_890_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_891_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_890_);
lean_dec_ref(v___x_889_);
if (v___x_891_ == 0)
{
lean_dec_ref(v_arg_886_);
lean_del_object(v___x_880_);
lean_dec_ref(v_e_813_);
v___y_835_ = v_a_814_;
v___y_836_ = v_a_815_;
v___y_837_ = v_a_816_;
v___y_838_ = v_a_817_;
goto v___jp_834_;
}
else
{
if (lean_obj_tag(v_arg_886_) == 9)
{
lean_object* v_a_892_; 
v_a_892_ = lean_ctor_get(v_arg_886_, 0);
lean_inc_ref(v_a_892_);
lean_dec_ref_known(v_arg_886_, 1);
if (lean_obj_tag(v_a_892_) == 0)
{
lean_object* v_val_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_905_; 
v_val_893_ = lean_ctor_get(v_a_892_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_a_892_);
if (v_isSharedCheck_905_ == 0)
{
v___x_895_ = v_a_892_;
v_isShared_896_ = v_isSharedCheck_905_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_val_893_);
lean_dec(v_a_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_905_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_nat_dec_eq(v_val_893_, v___x_897_);
lean_dec(v_val_893_);
if (v___x_898_ == 0)
{
lean_del_object(v___x_895_);
lean_del_object(v___x_880_);
lean_dec_ref(v_arg_833_);
goto v___jp_819_;
}
else
{
lean_object* v___x_900_; 
lean_dec_ref(v_e_813_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v_arg_833_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_arg_833_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_900_);
v___x_902_ = v___x_880_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_892_);
lean_del_object(v___x_880_);
lean_dec_ref(v_arg_833_);
goto v___jp_819_;
}
}
else
{
lean_dec_ref(v_arg_886_);
lean_del_object(v___x_880_);
lean_dec_ref(v_arg_833_);
goto v___jp_819_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_e_813_);
v_a_907_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_877_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_877_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
v___jp_834_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_getIntValue_x3f(v_arg_833_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_861_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_861_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_861_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_861_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (lean_obj_tag(v_a_840_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
lean_del_object(v___x_842_);
v_val_844_ = lean_ctor_get(v_a_840_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v_a_840_, 1);
v___x_845_ = lean_int_neg(v_val_844_);
lean_dec(v_val_844_);
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_847_ = lean_int_dec_le(v___x_846_, v___x_845_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_851_ = lean_int_neg(v___x_845_);
lean_dec(v___x_845_);
v___x_852_ = l_Int_toNat(v___x_851_);
lean_dec(v___x_851_);
v___x_853_ = l_Lean_instToExprInt_mkNat(v___x_852_);
v___x_854_ = l_Lean_mkApp3(v___x_848_, v___x_849_, v___x_850_, v___x_853_);
v___y_826_ = v___x_854_;
goto v___jp_825_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = l_Int_toNat(v___x_845_);
lean_dec(v___x_845_);
v___x_856_ = l_Lean_instToExprInt_mkNat(v___x_855_);
v___y_826_ = v___x_856_;
goto v___jp_825_;
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v_a_840_);
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_857_);
v___x_859_ = v___x_842_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_839_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_839_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_e_813_);
v_a_915_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_829_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_829_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
v___jp_819_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_e_813_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___y_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT void l_Int_reduceNeg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_813_ = stack[0].m_obj;
lean_object* v_a_814_ = stack[1].m_obj;
lean_object* v_a_815_ = stack[2].m_obj;
lean_object* v_a_816_ = stack[3].m_obj;
lean_object* v_a_817_ = stack[4].m_obj;
lean_object* v_res_923_;
v_res_923_ = l_Int_reduceNeg___redArg(v_e_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object* v_e_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Int_reduceNeg___redArg(v_e_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_930_;
}
}
lean_object* l_Int_reduceNeg(lean_object* v_e_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Int_reduceNeg___redArg(v_e_931_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_940_;
}
}
LEAN_EXPORT void l_Int_reduceNeg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_931_ = stack[0].m_obj;
lean_object* v_a_932_ = stack[1].m_obj;
lean_object* v_a_933_ = stack[2].m_obj;
lean_object* v_a_934_ = stack[3].m_obj;
lean_object* v_a_935_ = stack[4].m_obj;
lean_object* v_a_936_ = stack[5].m_obj;
lean_object* v_a_937_ = stack[6].m_obj;
lean_object* v_a_938_ = stack[7].m_obj;
lean_object* v_res_941_;
v_res_941_ = l_Int_reduceNeg(v_e_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object* v_e_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Int_reduceNeg(v_e_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
return v_res_951_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_974_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_975_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_972_, v___x_973_, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_976_;
v_res_976_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_();
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25____boxed(lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_();
return v_res_978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_983_ = 1;
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_);
v___x_985_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_982_, v___x_983_, v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_986_;
v_res_986_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_();
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27____boxed(lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_();
return v_res_988_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_991_ = 1;
v___x_992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_);
v___x_993_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_990_, v___x_991_, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_994_;
v_res_994_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_();
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29____boxed(lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_();
return v_res_996_;
}
}
lean_object* l_Int_isPosValue___redArg(lean_object* v_e_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1003_; 
lean_inc_ref(v_e_997_);
v___x_1003_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_997_, v_a_998_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1021_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1021_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1021_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = l_Lean_Expr_cleanupAnnotations(v_a_1004_);
v___x_1009_ = l_Lean_Expr_isApp(v___x_1008_);
if (v___x_1009_ == 0)
{
lean_dec_ref(v___x_1008_);
lean_del_object(v___x_1006_);
lean_dec_ref(v_e_997_);
goto v___jp_1000_;
}
else
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1008_);
v___x_1011_ = l_Lean_Expr_isApp(v___x_1010_);
if (v___x_1011_ == 0)
{
lean_dec_ref(v___x_1010_);
lean_del_object(v___x_1006_);
lean_dec_ref(v_e_997_);
goto v___jp_1000_;
}
else
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1010_);
v___x_1013_ = l_Lean_Expr_isApp(v___x_1012_);
if (v___x_1013_ == 0)
{
lean_dec_ref(v___x_1012_);
lean_del_object(v___x_1006_);
lean_dec_ref(v_e_997_);
goto v___jp_1000_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1012_);
v___x_1015_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_1016_ = l_Lean_Expr_isConstOf(v___x_1014_, v___x_1015_);
lean_dec_ref(v___x_1014_);
if (v___x_1016_ == 0)
{
lean_del_object(v___x_1006_);
lean_dec_ref(v_e_997_);
goto v___jp_1000_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_e_997_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1017_);
v___x_1019_ = v___x_1006_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_e_997_);
v_a_1022_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1003_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1003_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
v___jp_1000_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
}
LEAN_EXPORT void l_Int_isPosValue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_997_ = stack[0].m_obj;
lean_object* v_a_998_ = stack[1].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l_Int_isPosValue___redArg(v_e_997_, v_a_998_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object* v_e_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Int_isPosValue___redArg(v_e_1031_, v_a_1032_);
lean_dec(v_a_1032_);
return v_res_1034_;
}
}
lean_object* l_Int_isPosValue(lean_object* v_e_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Int_isPosValue___redArg(v_e_1035_, v_a_1040_);
return v___x_1044_;
}
}
LEAN_EXPORT void l_Int_isPosValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1035_ = stack[0].m_obj;
lean_object* v_a_1036_ = stack[1].m_obj;
lean_object* v_a_1037_ = stack[2].m_obj;
lean_object* v_a_1038_ = stack[3].m_obj;
lean_object* v_a_1039_ = stack[4].m_obj;
lean_object* v_a_1040_ = stack[5].m_obj;
lean_object* v_a_1041_ = stack[6].m_obj;
lean_object* v_a_1042_ = stack[7].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Int_isPosValue(v_e_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object* v_e_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Int_isPosValue(v_e_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
return v_res_1055_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1075_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1076_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1073_, v___x_1074_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1077_;
v_res_1077_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_();
stack->m_obj
 = v_res_1077_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23____boxed(lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_();
return v_res_1079_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1084_ = 1;
v___x_1085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_);
v___x_1086_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1083_, v___x_1084_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1087_;
v_res_1087_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_();
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25____boxed(lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_();
return v_res_1089_;
}
}
lean_object* l_Int_reduceAdd___redArg(lean_object* v_e_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1101_ = ((lean_object*)(l_Int_reduceAdd___redArg___closed__2));
v___x_1102_ = lean_unsigned_to_nat(6u);
v___x_1103_ = l_Lean_Expr_isAppOfArity(v_e_1095_, v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_Expr_appFn_x21(v_e_1095_);
v___x_1107_ = l_Lean_Expr_appArg_x21(v___x_1106_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = l_Lean_Meta_getIntValue_x3f(v___x_1107_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1162_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1162_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1162_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
if (lean_obj_tag(v_a_1109_) == 1)
{
lean_object* v_val_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1157_; 
v_val_1113_ = lean_ctor_get(v_a_1109_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_a_1109_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1115_ = v_a_1109_;
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_val_1113_);
lean_dec(v_a_1109_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = l_Lean_Expr_appArg_x21(v_e_1095_);
v___x_1118_ = l_Lean_Meta_getIntValue_x3f(v___x_1117_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1148_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1148_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1148_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___y_1124_; 
if (lean_obj_tag(v_a_1119_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
lean_del_object(v___x_1111_);
v_val_1131_ = lean_ctor_get(v_a_1119_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v_a_1119_, 1);
v___x_1132_ = lean_int_add(v_val_1113_, v_val_1131_);
lean_dec(v_val_1131_);
lean_dec(v_val_1113_);
v___x_1133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1134_ = lean_int_dec_le(v___x_1133_, v___x_1132_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1137_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1138_ = lean_int_neg(v___x_1132_);
lean_dec(v___x_1132_);
v___x_1139_ = l_Int_toNat(v___x_1138_);
lean_dec(v___x_1138_);
v___x_1140_ = l_Lean_instToExprInt_mkNat(v___x_1139_);
v___x_1141_ = l_Lean_mkApp3(v___x_1135_, v___x_1136_, v___x_1137_, v___x_1140_);
v___y_1124_ = v___x_1141_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = l_Int_toNat(v___x_1132_);
lean_dec(v___x_1132_);
v___x_1143_ = l_Lean_instToExprInt_mkNat(v___x_1142_);
v___y_1124_ = v___x_1143_;
goto v___jp_1123_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_del_object(v___x_1121_);
lean_dec(v_a_1119_);
lean_del_object(v___x_1115_);
lean_dec(v_val_1113_);
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1144_);
v___x_1146_ = v___x_1111_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
v___jp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 0);
lean_ctor_set(v___x_1115_, 0, v___y_1124_);
v___x_1126_ = v___x_1115_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___y_1124_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1126_);
v___x_1128_ = v___x_1121_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_del_object(v___x_1115_);
lean_dec(v_val_1113_);
lean_del_object(v___x_1111_);
v_a_1149_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1118_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1118_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_dec(v_a_1109_);
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1158_);
v___x_1160_ = v___x_1111_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1108_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1108_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceAdd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1095_ = stack[0].m_obj;
lean_object* v_a_1096_ = stack[1].m_obj;
lean_object* v_a_1097_ = stack[2].m_obj;
lean_object* v_a_1098_ = stack[3].m_obj;
lean_object* v_a_1099_ = stack[4].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l_Int_reduceAdd___redArg(v_e_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
stack->m_obj
 = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object* v_e_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Int_reduceAdd___redArg(v_e_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec_ref(v_e_1172_);
return v_res_1178_;
}
}
lean_object* l_Int_reduceAdd(lean_object* v_e_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Int_reduceAdd___redArg(v_e_1179_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT void l_Int_reduceAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1179_ = stack[0].m_obj;
lean_object* v_a_1180_ = stack[1].m_obj;
lean_object* v_a_1181_ = stack[2].m_obj;
lean_object* v_a_1182_ = stack[3].m_obj;
lean_object* v_a_1183_ = stack[4].m_obj;
lean_object* v_a_1184_ = stack[5].m_obj;
lean_object* v_a_1185_ = stack[6].m_obj;
lean_object* v_a_1186_ = stack[7].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l_Int_reduceAdd(v_e_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Int_reduceAdd(v_e_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_e_1190_);
return v_res_1199_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1222_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1223_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1220_, v___x_1221_, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1224_;
v_res_1224_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_();
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26____boxed(lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_();
return v_res_1226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1231_ = 1;
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_);
v___x_1233_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1230_, v___x_1231_, v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1234_;
v_res_1234_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_();
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28____boxed(lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_();
return v_res_1236_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1239_ = 1;
v___x_1240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_);
v___x_1241_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1238_, v___x_1239_, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1242_;
v_res_1242_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_();
stack->m_obj
 = v_res_1242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30____boxed(lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_();
return v_res_1244_;
}
}
lean_object* l_Int_reduceMul___redArg(lean_object* v_e_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = ((lean_object*)(l_Int_reduceMul___redArg___closed__2));
v___x_1257_ = lean_unsigned_to_nat(6u);
v___x_1258_ = l_Lean_Expr_isAppOfArity(v_e_1250_, v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = l_Lean_Expr_appFn_x21(v_e_1250_);
v___x_1262_ = l_Lean_Expr_appArg_x21(v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = l_Lean_Meta_getIntValue_x3f(v___x_1262_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1317_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1317_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1317_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
if (lean_obj_tag(v_a_1264_) == 1)
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1312_; 
v_val_1268_ = lean_ctor_get(v_a_1264_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_a_1264_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1270_ = v_a_1264_;
v_isShared_1271_ = v_isSharedCheck_1312_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v_a_1264_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1312_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_Lean_Expr_appArg_x21(v_e_1250_);
v___x_1273_ = l_Lean_Meta_getIntValue_x3f(v___x_1272_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1303_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1303_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1303_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___y_1279_; 
if (lean_obj_tag(v_a_1274_) == 1)
{
lean_object* v_val_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
lean_del_object(v___x_1266_);
v_val_1286_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v_a_1274_, 1);
v___x_1287_ = lean_int_mul(v_val_1268_, v_val_1286_);
lean_dec(v_val_1286_);
lean_dec(v_val_1268_);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1289_ = lean_int_dec_le(v___x_1288_, v___x_1287_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1293_ = lean_int_neg(v___x_1287_);
lean_dec(v___x_1287_);
v___x_1294_ = l_Int_toNat(v___x_1293_);
lean_dec(v___x_1293_);
v___x_1295_ = l_Lean_instToExprInt_mkNat(v___x_1294_);
v___x_1296_ = l_Lean_mkApp3(v___x_1290_, v___x_1291_, v___x_1292_, v___x_1295_);
v___y_1279_ = v___x_1296_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = l_Int_toNat(v___x_1287_);
lean_dec(v___x_1287_);
v___x_1298_ = l_Lean_instToExprInt_mkNat(v___x_1297_);
v___y_1279_ = v___x_1298_;
goto v___jp_1278_;
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_del_object(v___x_1276_);
lean_dec(v_a_1274_);
lean_del_object(v___x_1270_);
lean_dec(v_val_1268_);
v___x_1299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1299_);
v___x_1301_ = v___x_1266_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
v___jp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
lean_ctor_set(v___x_1270_, 0, v___y_1279_);
v___x_1281_ = v___x_1270_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___y_1279_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1281_);
v___x_1283_ = v___x_1276_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_del_object(v___x_1270_);
lean_dec(v_val_1268_);
lean_del_object(v___x_1266_);
v_a_1304_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1273_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1273_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_dec(v_a_1264_);
v___x_1313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1313_);
v___x_1315_ = v___x_1266_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1263_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1263_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceMul___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1250_ = stack[0].m_obj;
lean_object* v_a_1251_ = stack[1].m_obj;
lean_object* v_a_1252_ = stack[2].m_obj;
lean_object* v_a_1253_ = stack[3].m_obj;
lean_object* v_a_1254_ = stack[4].m_obj;
lean_object* v_res_1326_;
v_res_1326_ = l_Int_reduceMul___redArg(v_e_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
stack->m_obj
 = v_res_1326_;
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object* v_e_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Int_reduceMul___redArg(v_e_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_e_1327_);
return v_res_1333_;
}
}
lean_object* l_Int_reduceMul(lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Int_reduceMul___redArg(v_e_1334_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT void l_Int_reduceMul_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1334_ = stack[0].m_obj;
lean_object* v_a_1335_ = stack[1].m_obj;
lean_object* v_a_1336_ = stack[2].m_obj;
lean_object* v_a_1337_ = stack[3].m_obj;
lean_object* v_a_1338_ = stack[4].m_obj;
lean_object* v_a_1339_ = stack[5].m_obj;
lean_object* v_a_1340_ = stack[6].m_obj;
lean_object* v_a_1341_ = stack[7].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l_Int_reduceMul(v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
stack->m_obj
 = v_res_1344_;
}
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object* v_e_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Int_reduceMul(v_e_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_e_1345_);
return v_res_1354_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1377_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1378_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1375_, v___x_1376_, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1379_;
v_res_1379_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_();
stack->m_obj
 = v_res_1379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26____boxed(lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_();
return v_res_1381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1386_ = 1;
v___x_1387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_);
v___x_1388_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1385_, v___x_1386_, v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1389_;
v_res_1389_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_();
stack->m_obj
 = v_res_1389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28____boxed(lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_();
return v_res_1391_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1394_ = 1;
v___x_1395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_);
v___x_1396_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1393_, v___x_1394_, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1397_;
v_res_1397_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_();
stack->m_obj
 = v_res_1397_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30____boxed(lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_();
return v_res_1399_;
}
}
lean_object* l_Int_reduceSub___redArg(lean_object* v_e_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = ((lean_object*)(l_Int_reduceSub___redArg___closed__2));
v___x_1412_ = lean_unsigned_to_nat(6u);
v___x_1413_ = l_Lean_Expr_isAppOfArity(v_e_1405_, v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = l_Lean_Expr_appFn_x21(v_e_1405_);
v___x_1417_ = l_Lean_Expr_appArg_x21(v___x_1416_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = l_Lean_Meta_getIntValue_x3f(v___x_1417_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1472_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1472_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1472_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
if (lean_obj_tag(v_a_1419_) == 1)
{
lean_object* v_val_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1467_; 
v_val_1423_ = lean_ctor_get(v_a_1419_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_a_1419_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1425_ = v_a_1419_;
v_isShared_1426_ = v_isSharedCheck_1467_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_val_1423_);
lean_dec(v_a_1419_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1467_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = l_Lean_Expr_appArg_x21(v_e_1405_);
v___x_1428_ = l_Lean_Meta_getIntValue_x3f(v___x_1427_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1458_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1458_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1458_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___y_1434_; 
if (lean_obj_tag(v_a_1429_) == 1)
{
lean_object* v_val_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
lean_del_object(v___x_1421_);
v_val_1441_ = lean_ctor_get(v_a_1429_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v_a_1429_, 1);
v___x_1442_ = lean_int_sub(v_val_1423_, v_val_1441_);
lean_dec(v_val_1441_);
lean_dec(v_val_1423_);
v___x_1443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1444_ = lean_int_dec_le(v___x_1443_, v___x_1442_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1448_ = lean_int_neg(v___x_1442_);
lean_dec(v___x_1442_);
v___x_1449_ = l_Int_toNat(v___x_1448_);
lean_dec(v___x_1448_);
v___x_1450_ = l_Lean_instToExprInt_mkNat(v___x_1449_);
v___x_1451_ = l_Lean_mkApp3(v___x_1445_, v___x_1446_, v___x_1447_, v___x_1450_);
v___y_1434_ = v___x_1451_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = l_Int_toNat(v___x_1442_);
lean_dec(v___x_1442_);
v___x_1453_ = l_Lean_instToExprInt_mkNat(v___x_1452_);
v___y_1434_ = v___x_1453_;
goto v___jp_1433_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_del_object(v___x_1431_);
lean_dec(v_a_1429_);
lean_del_object(v___x_1425_);
lean_dec(v_val_1423_);
v___x_1454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1454_);
v___x_1456_ = v___x_1421_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
v___jp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set_tag(v___x_1425_, 0);
lean_ctor_set(v___x_1425_, 0, v___y_1434_);
v___x_1436_ = v___x_1425_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___y_1434_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1436_);
v___x_1438_ = v___x_1431_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_del_object(v___x_1425_);
lean_dec(v_val_1423_);
lean_del_object(v___x_1421_);
v_a_1459_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1428_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1428_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v_a_1419_);
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1468_);
v___x_1470_ = v___x_1421_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
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
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1418_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1418_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceSub___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1405_ = stack[0].m_obj;
lean_object* v_a_1406_ = stack[1].m_obj;
lean_object* v_a_1407_ = stack[2].m_obj;
lean_object* v_a_1408_ = stack[3].m_obj;
lean_object* v_a_1409_ = stack[4].m_obj;
lean_object* v_res_1481_;
v_res_1481_ = l_Int_reduceSub___redArg(v_e_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
stack->m_obj
 = v_res_1481_;
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object* v_e_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Int_reduceSub___redArg(v_e_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_e_1482_);
return v_res_1488_;
}
}
lean_object* l_Int_reduceSub(lean_object* v_e_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Int_reduceSub___redArg(v_e_1489_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT void l_Int_reduceSub_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1489_ = stack[0].m_obj;
lean_object* v_a_1490_ = stack[1].m_obj;
lean_object* v_a_1491_ = stack[2].m_obj;
lean_object* v_a_1492_ = stack[3].m_obj;
lean_object* v_a_1493_ = stack[4].m_obj;
lean_object* v_a_1494_ = stack[5].m_obj;
lean_object* v_a_1495_ = stack[6].m_obj;
lean_object* v_a_1496_ = stack[7].m_obj;
lean_object* v_res_1499_;
v_res_1499_ = l_Int_reduceSub(v_e_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
stack->m_obj
 = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Int_reduceSub(v_e_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_e_1500_);
return v_res_1509_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1532_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1533_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1530_, v___x_1531_, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1534_;
v_res_1534_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_();
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26____boxed(lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_();
return v_res_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1541_ = 1;
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_);
v___x_1543_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1540_, v___x_1541_, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1544_;
v_res_1544_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_();
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28____boxed(lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_();
return v_res_1546_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1549_ = 1;
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_);
v___x_1551_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1548_, v___x_1549_, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1552_;
v_res_1552_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_();
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30____boxed(lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_();
return v_res_1554_;
}
}
lean_object* l_Int_reduceDiv___redArg(lean_object* v_e_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1566_ = ((lean_object*)(l_Int_reduceDiv___redArg___closed__2));
v___x_1567_ = lean_unsigned_to_nat(6u);
v___x_1568_ = l_Lean_Expr_isAppOfArity(v_e_1560_, v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = l_Lean_Expr_appFn_x21(v_e_1560_);
v___x_1572_ = l_Lean_Expr_appArg_x21(v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = l_Lean_Meta_getIntValue_x3f(v___x_1572_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1627_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1627_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1627_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
if (lean_obj_tag(v_a_1574_) == 1)
{
lean_object* v_val_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1622_; 
v_val_1578_ = lean_ctor_get(v_a_1574_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1574_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1580_ = v_a_1574_;
v_isShared_1581_ = v_isSharedCheck_1622_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_val_1578_);
lean_dec(v_a_1574_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1622_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = l_Lean_Expr_appArg_x21(v_e_1560_);
v___x_1583_ = l_Lean_Meta_getIntValue_x3f(v___x_1582_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1613_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1613_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1613_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___y_1589_; 
if (lean_obj_tag(v_a_1584_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
lean_del_object(v___x_1576_);
v_val_1596_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_a_1584_, 1);
v___x_1597_ = lean_int_ediv(v_val_1578_, v_val_1596_);
lean_dec(v_val_1596_);
lean_dec(v_val_1578_);
v___x_1598_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1599_ = lean_int_dec_le(v___x_1598_, v___x_1597_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1603_ = lean_int_neg(v___x_1597_);
lean_dec(v___x_1597_);
v___x_1604_ = l_Int_toNat(v___x_1603_);
lean_dec(v___x_1603_);
v___x_1605_ = l_Lean_instToExprInt_mkNat(v___x_1604_);
v___x_1606_ = l_Lean_mkApp3(v___x_1600_, v___x_1601_, v___x_1602_, v___x_1605_);
v___y_1589_ = v___x_1606_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = l_Int_toNat(v___x_1597_);
lean_dec(v___x_1597_);
v___x_1608_ = l_Lean_instToExprInt_mkNat(v___x_1607_);
v___y_1589_ = v___x_1608_;
goto v___jp_1588_;
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
lean_del_object(v___x_1586_);
lean_dec(v_a_1584_);
lean_del_object(v___x_1580_);
lean_dec(v_val_1578_);
v___x_1609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1609_);
v___x_1611_ = v___x_1576_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
v___jp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 0);
lean_ctor_set(v___x_1580_, 0, v___y_1589_);
v___x_1591_ = v___x_1580_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___y_1589_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1591_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_del_object(v___x_1580_);
lean_dec(v_val_1578_);
lean_del_object(v___x_1576_);
v_a_1614_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1583_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1583_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
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
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_a_1574_);
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1623_);
v___x_1625_ = v___x_1576_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1573_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1573_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceDiv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1560_ = stack[0].m_obj;
lean_object* v_a_1561_ = stack[1].m_obj;
lean_object* v_a_1562_ = stack[2].m_obj;
lean_object* v_a_1563_ = stack[3].m_obj;
lean_object* v_a_1564_ = stack[4].m_obj;
lean_object* v_res_1636_;
v_res_1636_ = l_Int_reduceDiv___redArg(v_e_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object* v_e_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Int_reduceDiv___redArg(v_e_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec_ref(v_e_1637_);
return v_res_1643_;
}
}
lean_object* l_Int_reduceDiv(lean_object* v_e_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Int_reduceDiv___redArg(v_e_1644_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT void l_Int_reduceDiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1644_ = stack[0].m_obj;
lean_object* v_a_1645_ = stack[1].m_obj;
lean_object* v_a_1646_ = stack[2].m_obj;
lean_object* v_a_1647_ = stack[3].m_obj;
lean_object* v_a_1648_ = stack[4].m_obj;
lean_object* v_a_1649_ = stack[5].m_obj;
lean_object* v_a_1650_ = stack[6].m_obj;
lean_object* v_a_1651_ = stack[7].m_obj;
lean_object* v_res_1654_;
v_res_1654_ = l_Int_reduceDiv(v_e_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Int_reduceDiv(v_e_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_e_1655_);
return v_res_1664_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1687_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1688_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1685_, v___x_1686_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1689_;
v_res_1689_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_();
stack->m_obj
 = v_res_1689_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26____boxed(lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_();
return v_res_1691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1696_ = 1;
v___x_1697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_);
v___x_1698_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1695_, v___x_1696_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1699_;
v_res_1699_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_();
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28____boxed(lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_();
return v_res_1701_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1704_ = 1;
v___x_1705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_);
v___x_1706_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1703_, v___x_1704_, v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1707_;
v_res_1707_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_();
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30____boxed(lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_();
return v_res_1709_;
}
}
lean_object* l_Int_reduceMod___redArg(lean_object* v_e_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = ((lean_object*)(l_Int_reduceMod___redArg___closed__2));
v___x_1722_ = lean_unsigned_to_nat(6u);
v___x_1723_ = l_Lean_Expr_isAppOfArity(v_e_1715_, v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_Expr_appFn_x21(v_e_1715_);
v___x_1727_ = l_Lean_Expr_appArg_x21(v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = l_Lean_Meta_getIntValue_x3f(v___x_1727_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1782_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1782_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1782_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
if (lean_obj_tag(v_a_1729_) == 1)
{
lean_object* v_val_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1777_; 
v_val_1733_ = lean_ctor_get(v_a_1729_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_a_1729_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1735_ = v_a_1729_;
v_isShared_1736_ = v_isSharedCheck_1777_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_val_1733_);
lean_dec(v_a_1729_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1777_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = l_Lean_Expr_appArg_x21(v_e_1715_);
v___x_1738_ = l_Lean_Meta_getIntValue_x3f(v___x_1737_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1768_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1768_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1768_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___y_1744_; 
if (lean_obj_tag(v_a_1739_) == 1)
{
lean_object* v_val_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
lean_del_object(v___x_1731_);
v_val_1751_ = lean_ctor_get(v_a_1739_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v_a_1739_, 1);
v___x_1752_ = lean_int_emod(v_val_1733_, v_val_1751_);
lean_dec(v_val_1751_);
lean_dec(v_val_1733_);
v___x_1753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1754_ = lean_int_dec_le(v___x_1753_, v___x_1752_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1758_ = lean_int_neg(v___x_1752_);
lean_dec(v___x_1752_);
v___x_1759_ = l_Int_toNat(v___x_1758_);
lean_dec(v___x_1758_);
v___x_1760_ = l_Lean_instToExprInt_mkNat(v___x_1759_);
v___x_1761_ = l_Lean_mkApp3(v___x_1755_, v___x_1756_, v___x_1757_, v___x_1760_);
v___y_1744_ = v___x_1761_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = l_Int_toNat(v___x_1752_);
lean_dec(v___x_1752_);
v___x_1763_ = l_Lean_instToExprInt_mkNat(v___x_1762_);
v___y_1744_ = v___x_1763_;
goto v___jp_1743_;
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_del_object(v___x_1741_);
lean_dec(v_a_1739_);
lean_del_object(v___x_1735_);
lean_dec(v_val_1733_);
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1764_);
v___x_1766_ = v___x_1731_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
v___jp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 0);
lean_ctor_set(v___x_1735_, 0, v___y_1744_);
v___x_1746_ = v___x_1735_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___y_1744_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1746_);
v___x_1748_ = v___x_1741_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1735_);
lean_dec(v_val_1733_);
lean_del_object(v___x_1731_);
v_a_1769_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1738_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1738_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
lean_dec(v_a_1729_);
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1778_);
v___x_1780_ = v___x_1731_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1728_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1728_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
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
}
}
LEAN_EXPORT void l_Int_reduceMod___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1715_ = stack[0].m_obj;
lean_object* v_a_1716_ = stack[1].m_obj;
lean_object* v_a_1717_ = stack[2].m_obj;
lean_object* v_a_1718_ = stack[3].m_obj;
lean_object* v_a_1719_ = stack[4].m_obj;
lean_object* v_res_1791_;
v_res_1791_ = l_Int_reduceMod___redArg(v_e_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
stack->m_obj
 = v_res_1791_;
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object* v_e_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Int_reduceMod___redArg(v_e_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec_ref(v_e_1792_);
return v_res_1798_;
}
}
lean_object* l_Int_reduceMod(lean_object* v_e_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Int_reduceMod___redArg(v_e_1799_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT void l_Int_reduceMod_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1799_ = stack[0].m_obj;
lean_object* v_a_1800_ = stack[1].m_obj;
lean_object* v_a_1801_ = stack[2].m_obj;
lean_object* v_a_1802_ = stack[3].m_obj;
lean_object* v_a_1803_ = stack[4].m_obj;
lean_object* v_a_1804_ = stack[5].m_obj;
lean_object* v_a_1805_ = stack[6].m_obj;
lean_object* v_a_1806_ = stack[7].m_obj;
lean_object* v_res_1809_;
v_res_1809_ = l_Int_reduceMod(v_e_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
stack->m_obj
 = v_res_1809_;
}
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object* v_e_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Int_reduceMod(v_e_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_e_1810_);
return v_res_1819_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1842_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1843_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1840_, v___x_1841_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1844_;
v_res_1844_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_();
stack->m_obj
 = v_res_1844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26____boxed(lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_();
return v_res_1846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1851_ = 1;
v___x_1852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_);
v___x_1853_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1850_, v___x_1851_, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1854_;
v_res_1854_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_();
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28____boxed(lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_();
return v_res_1856_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1859_ = 1;
v___x_1860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_);
v___x_1861_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1858_, v___x_1859_, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1862_;
v_res_1862_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_();
stack->m_obj
 = v_res_1862_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30____boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_();
return v_res_1864_;
}
}
lean_object* l_Int_reduceTDiv___redArg(lean_object* v_e_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1875_ = ((lean_object*)(l_Int_reduceTDiv___redArg___closed__1));
v___x_1876_ = lean_unsigned_to_nat(2u);
v___x_1877_ = l_Lean_Expr_isAppOfArity(v_e_1869_, v___x_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = l_Lean_Expr_appFn_x21(v_e_1869_);
v___x_1881_ = l_Lean_Expr_appArg_x21(v___x_1880_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_Meta_getIntValue_x3f(v___x_1881_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1936_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1936_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1936_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
if (lean_obj_tag(v_a_1883_) == 1)
{
lean_object* v_val_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1931_; 
v_val_1887_ = lean_ctor_get(v_a_1883_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_a_1883_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1889_ = v_a_1883_;
v_isShared_1890_ = v_isSharedCheck_1931_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_val_1887_);
lean_dec(v_a_1883_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1931_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = l_Lean_Expr_appArg_x21(v_e_1869_);
v___x_1892_ = l_Lean_Meta_getIntValue_x3f(v___x_1891_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1922_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1922_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1922_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___y_1898_; 
if (lean_obj_tag(v_a_1893_) == 1)
{
lean_object* v_val_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
lean_del_object(v___x_1885_);
v_val_1905_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_val_1905_);
lean_dec_ref_known(v_a_1893_, 1);
v___x_1906_ = lean_int_div(v_val_1887_, v_val_1905_);
lean_dec(v_val_1905_);
lean_dec(v_val_1887_);
v___x_1907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1908_ = lean_int_dec_le(v___x_1907_, v___x_1906_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1912_ = lean_int_neg(v___x_1906_);
lean_dec(v___x_1906_);
v___x_1913_ = l_Int_toNat(v___x_1912_);
lean_dec(v___x_1912_);
v___x_1914_ = l_Lean_instToExprInt_mkNat(v___x_1913_);
v___x_1915_ = l_Lean_mkApp3(v___x_1909_, v___x_1910_, v___x_1911_, v___x_1914_);
v___y_1898_ = v___x_1915_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = l_Int_toNat(v___x_1906_);
lean_dec(v___x_1906_);
v___x_1917_ = l_Lean_instToExprInt_mkNat(v___x_1916_);
v___y_1898_ = v___x_1917_;
goto v___jp_1897_;
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_del_object(v___x_1895_);
lean_dec(v_a_1893_);
lean_del_object(v___x_1889_);
lean_dec(v_val_1887_);
v___x_1918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1918_);
v___x_1920_ = v___x_1885_;
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
v___jp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
lean_ctor_set(v___x_1889_, 0, v___y_1898_);
v___x_1900_ = v___x_1889_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___y_1898_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1900_);
v___x_1902_ = v___x_1895_;
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
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_del_object(v___x_1889_);
lean_dec(v_val_1887_);
lean_del_object(v___x_1885_);
v_a_1923_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1892_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1892_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
lean_dec(v_a_1883_);
v___x_1932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1932_);
v___x_1934_ = v___x_1885_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
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
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1882_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1882_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceTDiv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1869_ = stack[0].m_obj;
lean_object* v_a_1870_ = stack[1].m_obj;
lean_object* v_a_1871_ = stack[2].m_obj;
lean_object* v_a_1872_ = stack[3].m_obj;
lean_object* v_a_1873_ = stack[4].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l_Int_reduceTDiv___redArg(v_e_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object* v_e_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Int_reduceTDiv___redArg(v_e_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_e_1946_);
return v_res_1952_;
}
}
lean_object* l_Int_reduceTDiv(lean_object* v_e_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Int_reduceTDiv___redArg(v_e_1953_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT void l_Int_reduceTDiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1953_ = stack[0].m_obj;
lean_object* v_a_1954_ = stack[1].m_obj;
lean_object* v_a_1955_ = stack[2].m_obj;
lean_object* v_a_1956_ = stack[3].m_obj;
lean_object* v_a_1957_ = stack[4].m_obj;
lean_object* v_a_1958_ = stack[5].m_obj;
lean_object* v_a_1959_ = stack[6].m_obj;
lean_object* v_a_1960_ = stack[7].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_Int_reduceTDiv(v_e_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object* v_e_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Int_reduceTDiv(v_e_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_e_1964_);
return v_res_1973_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1991_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1992_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1989_, v___x_1990_, v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1993_;
v_res_1993_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_();
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21____boxed(lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_();
return v_res_1995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
return v___x_1997_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_2000_ = 1;
v___x_2001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_);
v___x_2002_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1999_, v___x_2000_, v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2003_;
v_res_2003_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_();
stack->m_obj
 = v_res_2003_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23____boxed(lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_();
return v_res_2005_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_2008_ = 1;
v___x_2009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_);
v___x_2010_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2007_, v___x_2008_, v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2011_;
v_res_2011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_();
stack->m_obj
 = v_res_2011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25____boxed(lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_();
return v_res_2013_;
}
}
lean_object* l_Int_reduceTMod___redArg(lean_object* v_e_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2024_ = ((lean_object*)(l_Int_reduceTMod___redArg___closed__1));
v___x_2025_ = lean_unsigned_to_nat(2u);
v___x_2026_ = l_Lean_Expr_isAppOfArity(v_e_2018_, v___x_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_Expr_appFn_x21(v_e_2018_);
v___x_2030_ = l_Lean_Expr_appArg_x21(v___x_2029_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = l_Lean_Meta_getIntValue_x3f(v___x_2030_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2085_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2085_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2085_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
if (lean_obj_tag(v_a_2032_) == 1)
{
lean_object* v_val_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2080_; 
v_val_2036_ = lean_ctor_get(v_a_2032_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2032_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2038_ = v_a_2032_;
v_isShared_2039_ = v_isSharedCheck_2080_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_val_2036_);
lean_dec(v_a_2032_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2080_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = l_Lean_Expr_appArg_x21(v_e_2018_);
v___x_2041_ = l_Lean_Meta_getIntValue_x3f(v___x_2040_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2071_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2071_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2071_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___y_2047_; 
if (lean_obj_tag(v_a_2042_) == 1)
{
lean_object* v_val_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
lean_del_object(v___x_2034_);
v_val_2054_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_val_2054_);
lean_dec_ref_known(v_a_2042_, 1);
v___x_2055_ = lean_int_mod(v_val_2036_, v_val_2054_);
lean_dec(v_val_2054_);
lean_dec(v_val_2036_);
v___x_2056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2057_ = lean_int_dec_le(v___x_2056_, v___x_2055_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2061_ = lean_int_neg(v___x_2055_);
lean_dec(v___x_2055_);
v___x_2062_ = l_Int_toNat(v___x_2061_);
lean_dec(v___x_2061_);
v___x_2063_ = l_Lean_instToExprInt_mkNat(v___x_2062_);
v___x_2064_ = l_Lean_mkApp3(v___x_2058_, v___x_2059_, v___x_2060_, v___x_2063_);
v___y_2047_ = v___x_2064_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = l_Int_toNat(v___x_2055_);
lean_dec(v___x_2055_);
v___x_2066_ = l_Lean_instToExprInt_mkNat(v___x_2065_);
v___y_2047_ = v___x_2066_;
goto v___jp_2046_;
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_del_object(v___x_2044_);
lean_dec(v_a_2042_);
lean_del_object(v___x_2038_);
lean_dec(v_val_2036_);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2067_);
v___x_2069_ = v___x_2034_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
v___jp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 0);
lean_ctor_set(v___x_2038_, 0, v___y_2047_);
v___x_2049_ = v___x_2038_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___y_2047_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2049_);
v___x_2051_ = v___x_2044_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_del_object(v___x_2038_);
lean_dec(v_val_2036_);
lean_del_object(v___x_2034_);
v_a_2072_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2041_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2041_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
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
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
lean_dec(v_a_2032_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2081_);
v___x_2083_ = v___x_2034_;
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
v_a_2086_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2031_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2031_);
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
}
}
LEAN_EXPORT void l_Int_reduceTMod___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2018_ = stack[0].m_obj;
lean_object* v_a_2019_ = stack[1].m_obj;
lean_object* v_a_2020_ = stack[2].m_obj;
lean_object* v_a_2021_ = stack[3].m_obj;
lean_object* v_a_2022_ = stack[4].m_obj;
lean_object* v_res_2094_;
v_res_2094_ = l_Int_reduceTMod___redArg(v_e_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
stack->m_obj
 = v_res_2094_;
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object* v_e_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Int_reduceTMod___redArg(v_e_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec_ref(v_e_2095_);
return v_res_2101_;
}
}
lean_object* l_Int_reduceTMod(lean_object* v_e_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Int_reduceTMod___redArg(v_e_2102_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT void l_Int_reduceTMod_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2102_ = stack[0].m_obj;
lean_object* v_a_2103_ = stack[1].m_obj;
lean_object* v_a_2104_ = stack[2].m_obj;
lean_object* v_a_2105_ = stack[3].m_obj;
lean_object* v_a_2106_ = stack[4].m_obj;
lean_object* v_a_2107_ = stack[5].m_obj;
lean_object* v_a_2108_ = stack[6].m_obj;
lean_object* v_a_2109_ = stack[7].m_obj;
lean_object* v_res_2112_;
v_res_2112_ = l_Int_reduceTMod(v_e_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
stack->m_obj
 = v_res_2112_;
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object* v_e_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Int_reduceTMod(v_e_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_e_2113_);
return v_res_2122_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2140_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2141_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2138_, v___x_2139_, v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2142_;
v_res_2142_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_();
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21____boxed(lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_();
return v_res_2144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2149_ = 1;
v___x_2150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_);
v___x_2151_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2148_, v___x_2149_, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2152_;
v_res_2152_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_();
stack->m_obj
 = v_res_2152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23____boxed(lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_();
return v_res_2154_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2157_ = 1;
v___x_2158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_);
v___x_2159_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2156_, v___x_2157_, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2160_;
v_res_2160_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_();
stack->m_obj
 = v_res_2160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25____boxed(lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_();
return v_res_2162_;
}
}
lean_object* l_Int_reduceFDiv___redArg(lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = ((lean_object*)(l_Int_reduceFDiv___redArg___closed__1));
v___x_2174_ = lean_unsigned_to_nat(2u);
v___x_2175_ = l_Lean_Expr_isAppOfArity(v_e_2167_, v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = l_Lean_Expr_appFn_x21(v_e_2167_);
v___x_2179_ = l_Lean_Expr_appArg_x21(v___x_2178_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = l_Lean_Meta_getIntValue_x3f(v___x_2179_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2234_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2234_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2234_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
if (lean_obj_tag(v_a_2181_) == 1)
{
lean_object* v_val_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2229_; 
v_val_2185_ = lean_ctor_get(v_a_2181_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_a_2181_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2187_ = v_a_2181_;
v_isShared_2188_ = v_isSharedCheck_2229_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_val_2185_);
lean_dec(v_a_2181_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2229_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l_Lean_Expr_appArg_x21(v_e_2167_);
v___x_2190_ = l_Lean_Meta_getIntValue_x3f(v___x_2189_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2220_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2220_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2220_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___y_2196_; 
if (lean_obj_tag(v_a_2191_) == 1)
{
lean_object* v_val_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
lean_del_object(v___x_2183_);
v_val_2203_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v_a_2191_, 1);
v___x_2204_ = l_Int_fdiv(v_val_2185_, v_val_2203_);
lean_dec(v_val_2203_);
lean_dec(v_val_2185_);
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2206_ = lean_int_dec_le(v___x_2205_, v___x_2204_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2210_ = lean_int_neg(v___x_2204_);
lean_dec(v___x_2204_);
v___x_2211_ = l_Int_toNat(v___x_2210_);
lean_dec(v___x_2210_);
v___x_2212_ = l_Lean_instToExprInt_mkNat(v___x_2211_);
v___x_2213_ = l_Lean_mkApp3(v___x_2207_, v___x_2208_, v___x_2209_, v___x_2212_);
v___y_2196_ = v___x_2213_;
goto v___jp_2195_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = l_Int_toNat(v___x_2204_);
lean_dec(v___x_2204_);
v___x_2215_ = l_Lean_instToExprInt_mkNat(v___x_2214_);
v___y_2196_ = v___x_2215_;
goto v___jp_2195_;
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_del_object(v___x_2193_);
lean_dec(v_a_2191_);
lean_del_object(v___x_2187_);
lean_dec(v_val_2185_);
v___x_2216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2216_);
v___x_2218_ = v___x_2183_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
v___jp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set_tag(v___x_2187_, 0);
lean_ctor_set(v___x_2187_, 0, v___y_2196_);
v___x_2198_ = v___x_2187_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___y_2196_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2198_);
v___x_2200_ = v___x_2193_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_del_object(v___x_2187_);
lean_dec(v_val_2185_);
lean_del_object(v___x_2183_);
v_a_2221_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2190_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2190_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
lean_dec(v_a_2181_);
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2230_);
v___x_2232_ = v___x_2183_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
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
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_a_2235_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2180_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2180_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceFDiv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2167_ = stack[0].m_obj;
lean_object* v_a_2168_ = stack[1].m_obj;
lean_object* v_a_2169_ = stack[2].m_obj;
lean_object* v_a_2170_ = stack[3].m_obj;
lean_object* v_a_2171_ = stack[4].m_obj;
lean_object* v_res_2243_;
v_res_2243_ = l_Int_reduceFDiv___redArg(v_e_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
stack->m_obj
 = v_res_2243_;
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object* v_e_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Int_reduceFDiv___redArg(v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec_ref(v_e_2244_);
return v_res_2250_;
}
}
lean_object* l_Int_reduceFDiv(lean_object* v_e_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Int_reduceFDiv___redArg(v_e_2251_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT void l_Int_reduceFDiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2251_ = stack[0].m_obj;
lean_object* v_a_2252_ = stack[1].m_obj;
lean_object* v_a_2253_ = stack[2].m_obj;
lean_object* v_a_2254_ = stack[3].m_obj;
lean_object* v_a_2255_ = stack[4].m_obj;
lean_object* v_a_2256_ = stack[5].m_obj;
lean_object* v_a_2257_ = stack[6].m_obj;
lean_object* v_a_2258_ = stack[7].m_obj;
lean_object* v_res_2261_;
v_res_2261_ = l_Int_reduceFDiv(v_e_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
stack->m_obj
 = v_res_2261_;
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Int_reduceFDiv(v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
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
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2289_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2290_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2287_, v___x_2288_, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2291_;
v_res_2291_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_();
stack->m_obj
 = v_res_2291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21____boxed(lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_();
return v_res_2293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2298_ = 1;
v___x_2299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_);
v___x_2300_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2297_, v___x_2298_, v___x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2301_;
v_res_2301_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_();
stack->m_obj
 = v_res_2301_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23____boxed(lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_();
return v_res_2303_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2306_ = 1;
v___x_2307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_);
v___x_2308_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2305_, v___x_2306_, v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2309_;
v_res_2309_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_();
stack->m_obj
 = v_res_2309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25____boxed(lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_();
return v_res_2311_;
}
}
lean_object* l_Int_reduceFMod___redArg(lean_object* v_e_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2322_ = ((lean_object*)(l_Int_reduceFMod___redArg___closed__1));
v___x_2323_ = lean_unsigned_to_nat(2u);
v___x_2324_ = l_Lean_Expr_isAppOfArity(v_e_2316_, v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = l_Lean_Expr_appFn_x21(v_e_2316_);
v___x_2328_ = l_Lean_Expr_appArg_x21(v___x_2327_);
lean_dec_ref(v___x_2327_);
v___x_2329_ = l_Lean_Meta_getIntValue_x3f(v___x_2328_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2383_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2383_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2383_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
if (lean_obj_tag(v_a_2330_) == 1)
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2378_; 
v_val_2334_ = lean_ctor_get(v_a_2330_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2336_ = v_a_2330_;
v_isShared_2337_ = v_isSharedCheck_2378_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v_a_2330_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2378_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = l_Lean_Expr_appArg_x21(v_e_2316_);
v___x_2339_ = l_Lean_Meta_getIntValue_x3f(v___x_2338_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2369_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2369_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2369_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___y_2345_; 
if (lean_obj_tag(v_a_2340_) == 1)
{
lean_object* v_val_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
lean_del_object(v___x_2332_);
v_val_2352_ = lean_ctor_get(v_a_2340_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v_a_2340_, 1);
v___x_2353_ = l_Int_fmod(v_val_2334_, v_val_2352_);
lean_dec(v_val_2352_);
lean_dec(v_val_2334_);
v___x_2354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2355_ = lean_int_dec_le(v___x_2354_, v___x_2353_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2359_ = lean_int_neg(v___x_2353_);
lean_dec(v___x_2353_);
v___x_2360_ = l_Int_toNat(v___x_2359_);
lean_dec(v___x_2359_);
v___x_2361_ = l_Lean_instToExprInt_mkNat(v___x_2360_);
v___x_2362_ = l_Lean_mkApp3(v___x_2356_, v___x_2357_, v___x_2358_, v___x_2361_);
v___y_2345_ = v___x_2362_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = l_Int_toNat(v___x_2353_);
lean_dec(v___x_2353_);
v___x_2364_ = l_Lean_instToExprInt_mkNat(v___x_2363_);
v___y_2345_ = v___x_2364_;
goto v___jp_2344_;
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
lean_del_object(v___x_2342_);
lean_dec(v_a_2340_);
lean_del_object(v___x_2336_);
lean_dec(v_val_2334_);
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2365_);
v___x_2367_ = v___x_2332_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
v___jp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 0);
lean_ctor_set(v___x_2336_, 0, v___y_2345_);
v___x_2347_ = v___x_2336_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___y_2345_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2347_);
v___x_2349_ = v___x_2342_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_del_object(v___x_2336_);
lean_dec(v_val_2334_);
lean_del_object(v___x_2332_);
v_a_2370_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2339_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2339_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_dec(v_a_2330_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2379_);
v___x_2381_ = v___x_2332_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_a_2384_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2329_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2329_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceFMod___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2316_ = stack[0].m_obj;
lean_object* v_a_2317_ = stack[1].m_obj;
lean_object* v_a_2318_ = stack[2].m_obj;
lean_object* v_a_2319_ = stack[3].m_obj;
lean_object* v_a_2320_ = stack[4].m_obj;
lean_object* v_res_2392_;
v_res_2392_ = l_Int_reduceFMod___redArg(v_e_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
stack->m_obj
 = v_res_2392_;
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object* v_e_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Int_reduceFMod___redArg(v_e_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec_ref(v_e_2393_);
return v_res_2399_;
}
}
lean_object* l_Int_reduceFMod(lean_object* v_e_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Int_reduceFMod___redArg(v_e_2400_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT void l_Int_reduceFMod_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2400_ = stack[0].m_obj;
lean_object* v_a_2401_ = stack[1].m_obj;
lean_object* v_a_2402_ = stack[2].m_obj;
lean_object* v_a_2403_ = stack[3].m_obj;
lean_object* v_a_2404_ = stack[4].m_obj;
lean_object* v_a_2405_ = stack[5].m_obj;
lean_object* v_a_2406_ = stack[6].m_obj;
lean_object* v_a_2407_ = stack[7].m_obj;
lean_object* v_res_2410_;
v_res_2410_ = l_Int_reduceFMod(v_e_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
stack->m_obj
 = v_res_2410_;
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object* v_e_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Int_reduceFMod(v_e_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_e_2411_);
return v_res_2420_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2438_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2439_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2436_, v___x_2437_, v___x_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2440_;
v_res_2440_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_();
stack->m_obj
 = v_res_2440_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21____boxed(lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_();
return v_res_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2447_ = 1;
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_);
v___x_2449_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2446_, v___x_2447_, v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2450_;
v_res_2450_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_();
stack->m_obj
 = v_res_2450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23____boxed(lean_object* v_a_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_();
return v_res_2452_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2455_ = 1;
v___x_2456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_);
v___x_2457_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2454_, v___x_2455_, v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2458_;
v_res_2458_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_();
stack->m_obj
 = v_res_2458_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25____boxed(lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_();
return v_res_2460_;
}
}
lean_object* l_Int_reduceBdiv___redArg(lean_object* v_e_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__1));
v___x_2473_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__2));
v___x_2474_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v___x_2472_, v___x_2473_, v_e_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
return v___x_2474_;
}
}
LEAN_EXPORT void l_Int_reduceBdiv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2466_ = stack[0].m_obj;
lean_object* v_a_2467_ = stack[1].m_obj;
lean_object* v_a_2468_ = stack[2].m_obj;
lean_object* v_a_2469_ = stack[3].m_obj;
lean_object* v_a_2470_ = stack[4].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l_Int_reduceBdiv___redArg(v_e_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object* v_e_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Int_reduceBdiv___redArg(v_e_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec_ref(v_e_2476_);
return v_res_2482_;
}
}
lean_object* l_Int_reduceBdiv(lean_object* v_e_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Int_reduceBdiv___redArg(v_e_2483_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT void l_Int_reduceBdiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2483_ = stack[0].m_obj;
lean_object* v_a_2484_ = stack[1].m_obj;
lean_object* v_a_2485_ = stack[2].m_obj;
lean_object* v_a_2486_ = stack[3].m_obj;
lean_object* v_a_2487_ = stack[4].m_obj;
lean_object* v_a_2488_ = stack[5].m_obj;
lean_object* v_a_2489_ = stack[6].m_obj;
lean_object* v_a_2490_ = stack[7].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l_Int_reduceBdiv(v_e_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object* v_e_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Int_reduceBdiv(v_e_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_e_2494_);
return v_res_2503_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2521_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2522_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2519_, v___x_2520_, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2523_;
v_res_2523_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_();
stack->m_obj
 = v_res_2523_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21____boxed(lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_();
return v_res_2525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2530_ = 1;
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_);
v___x_2532_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2529_, v___x_2530_, v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2533_;
v_res_2533_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_();
stack->m_obj
 = v_res_2533_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23____boxed(lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_();
return v_res_2535_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2538_ = 1;
v___x_2539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_);
v___x_2540_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2537_, v___x_2538_, v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2541_;
v_res_2541_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_();
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25____boxed(lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_();
return v_res_2543_;
}
}
lean_object* l_Int_reduceBmod___redArg(lean_object* v_e_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__1));
v___x_2556_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__2));
v___x_2557_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v___x_2555_, v___x_2556_, v_e_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
return v___x_2557_;
}
}
LEAN_EXPORT void l_Int_reduceBmod___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2549_ = stack[0].m_obj;
lean_object* v_a_2550_ = stack[1].m_obj;
lean_object* v_a_2551_ = stack[2].m_obj;
lean_object* v_a_2552_ = stack[3].m_obj;
lean_object* v_a_2553_ = stack[4].m_obj;
lean_object* v_res_2558_;
v_res_2558_ = l_Int_reduceBmod___redArg(v_e_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
stack->m_obj
 = v_res_2558_;
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object* v_e_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Int_reduceBmod___redArg(v_e_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec_ref(v_e_2559_);
return v_res_2565_;
}
}
lean_object* l_Int_reduceBmod(lean_object* v_e_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Int_reduceBmod___redArg(v_e_2566_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT void l_Int_reduceBmod_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2566_ = stack[0].m_obj;
lean_object* v_a_2567_ = stack[1].m_obj;
lean_object* v_a_2568_ = stack[2].m_obj;
lean_object* v_a_2569_ = stack[3].m_obj;
lean_object* v_a_2570_ = stack[4].m_obj;
lean_object* v_a_2571_ = stack[5].m_obj;
lean_object* v_a_2572_ = stack[6].m_obj;
lean_object* v_a_2573_ = stack[7].m_obj;
lean_object* v_res_2576_;
v_res_2576_ = l_Int_reduceBmod(v_e_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
stack->m_obj
 = v_res_2576_;
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object* v_e_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Int_reduceBmod(v_e_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_e_2577_);
return v_res_2586_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2604_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2605_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2602_, v___x_2603_, v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2606_;
v_res_2606_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_();
stack->m_obj
 = v_res_2606_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21____boxed(lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_();
return v_res_2608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2613_ = 1;
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_);
v___x_2615_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2612_, v___x_2613_, v___x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2616_;
v_res_2616_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_();
stack->m_obj
 = v_res_2616_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23____boxed(lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_();
return v_res_2618_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2621_ = 1;
v___x_2622_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_);
v___x_2623_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2620_, v___x_2621_, v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2624_;
v_res_2624_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_();
stack->m_obj
 = v_res_2624_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25____boxed(lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_();
return v_res_2626_;
}
}
lean_object* l_Int_reducePow___redArg(lean_object* v_e_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2632_, v_a_2635_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = l_Lean_Expr_cleanupAnnotations(v_a_2643_);
v___x_2645_ = l_Lean_Expr_isApp(v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v___x_2644_);
goto v___jp_2639_;
}
else
{
lean_object* v_arg_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_arg_2646_ = lean_ctor_get(v___x_2644_, 1);
lean_inc_ref(v_arg_2646_);
v___x_2647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2644_);
v___x_2648_ = l_Lean_Expr_isApp(v___x_2647_);
if (v___x_2648_ == 0)
{
lean_dec_ref(v___x_2647_);
lean_dec_ref(v_arg_2646_);
goto v___jp_2639_;
}
else
{
lean_object* v_arg_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v_arg_2649_ = lean_ctor_get(v___x_2647_, 1);
lean_inc_ref(v_arg_2649_);
v___x_2650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2647_);
v___x_2651_ = l_Lean_Expr_isApp(v___x_2650_);
if (v___x_2651_ == 0)
{
lean_dec_ref(v___x_2650_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
goto v___jp_2639_;
}
else
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2650_);
v___x_2653_ = l_Lean_Expr_isApp(v___x_2652_);
if (v___x_2653_ == 0)
{
lean_dec_ref(v___x_2652_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
goto v___jp_2639_;
}
else
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2652_);
v___x_2655_ = l_Lean_Expr_isApp(v___x_2654_);
if (v___x_2655_ == 0)
{
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
goto v___jp_2639_;
}
else
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2654_);
v___x_2657_ = l_Lean_Expr_isApp(v___x_2656_);
if (v___x_2657_ == 0)
{
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
goto v___jp_2639_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2656_);
v___x_2659_ = ((lean_object*)(l_Int_reducePow___redArg___closed__2));
v___x_2660_ = l_Lean_Expr_isConstOf(v___x_2658_, v___x_2659_);
lean_dec_ref(v___x_2658_);
if (v___x_2660_ == 0)
{
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
goto v___jp_2639_;
}
else
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Meta_getIntValue_x3f(v_arg_2649_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2735_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2735_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2735_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
if (lean_obj_tag(v_a_2662_) == 1)
{
lean_object* v_val_2666_; lean_object* v___x_2667_; 
lean_del_object(v___x_2664_);
v_val_2666_ = lean_ctor_get(v_a_2662_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v_a_2662_, 1);
v___x_2667_ = l_Lean_Meta_getNatValue_x3f(v_arg_2646_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
lean_dec_ref(v_arg_2646_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2722_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2722_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2722_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
if (lean_obj_tag(v_a_2668_) == 1)
{
lean_object* v_config_2672_; lean_object* v_val_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2717_; 
v_config_2672_ = lean_ctor_get(v_a_2633_, 0);
v_val_2673_ = lean_ctor_get(v_a_2668_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_a_2668_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2675_ = v_a_2668_;
v_isShared_2676_ = v_isSharedCheck_2717_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_val_2673_);
lean_dec(v_a_2668_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2717_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
uint8_t v_warnExponents_2677_; lean_object* v___x_2678_; 
v_warnExponents_2677_ = lean_ctor_get_uint8(v_config_2672_, sizeof(void*)*3 + 25);
lean_inc(v_val_2673_);
v___x_2678_ = l_Lean_checkExponent(v_val_2673_, v_warnExponents_2677_, v_a_2636_, v_a_2637_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2708_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2708_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2708_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___y_2684_; uint8_t v___x_2691_; 
v___x_2691_ = lean_unbox(v_a_2679_);
lean_dec(v_a_2679_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
lean_del_object(v___x_2681_);
lean_del_object(v___x_2675_);
lean_dec(v_val_2673_);
lean_dec(v_val_2666_);
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2692_);
v___x_2694_ = v___x_2670_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
lean_del_object(v___x_2670_);
v___x_2696_ = l_Int_pow(v_val_2666_, v_val_2673_);
lean_dec(v_val_2673_);
lean_dec(v_val_2666_);
v___x_2697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2698_ = lean_int_dec_le(v___x_2697_, v___x_2696_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2702_ = lean_int_neg(v___x_2696_);
lean_dec(v___x_2696_);
v___x_2703_ = l_Int_toNat(v___x_2702_);
lean_dec(v___x_2702_);
v___x_2704_ = l_Lean_instToExprInt_mkNat(v___x_2703_);
v___x_2705_ = l_Lean_mkApp3(v___x_2699_, v___x_2700_, v___x_2701_, v___x_2704_);
v___y_2684_ = v___x_2705_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = l_Int_toNat(v___x_2696_);
lean_dec(v___x_2696_);
v___x_2707_ = l_Lean_instToExprInt_mkNat(v___x_2706_);
v___y_2684_ = v___x_2707_;
goto v___jp_2683_;
}
}
v___jp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 0);
lean_ctor_set(v___x_2675_, 0, v___y_2684_);
v___x_2686_ = v___x_2675_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___y_2684_);
v___x_2686_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2688_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2686_);
v___x_2688_ = v___x_2681_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_del_object(v___x_2675_);
lean_dec(v_val_2673_);
lean_del_object(v___x_2670_);
lean_dec(v_val_2666_);
v_a_2709_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2678_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2678_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_dec(v_a_2668_);
lean_dec(v_val_2666_);
v___x_2718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2718_);
v___x_2720_ = v___x_2670_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_val_2666_);
v_a_2723_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2667_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2667_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v_a_2662_);
lean_dec_ref(v_arg_2646_);
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2731_);
v___x_2733_ = v___x_2664_;
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
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v_arg_2646_);
v_a_2736_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2661_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2661_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
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
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_a_2744_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2642_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2642_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
v___jp_2639_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
}
}
LEAN_EXPORT void l_Int_reducePow___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2632_ = stack[0].m_obj;
lean_object* v_a_2633_ = stack[1].m_obj;
lean_object* v_a_2634_ = stack[2].m_obj;
lean_object* v_a_2635_ = stack[3].m_obj;
lean_object* v_a_2636_ = stack[4].m_obj;
lean_object* v_a_2637_ = stack[5].m_obj;
lean_object* v_res_2752_;
v_res_2752_ = l_Int_reducePow___redArg(v_e_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
stack->m_obj
 = v_res_2752_;
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object* v_e_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Int_reducePow___redArg(v_e_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec_ref(v_a_2754_);
return v_res_2760_;
}
}
lean_object* l_Int_reducePow(lean_object* v_e_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Int_reducePow___redArg(v_e_2761_, v_a_2763_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT void l_Int_reducePow_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2761_ = stack[0].m_obj;
lean_object* v_a_2762_ = stack[1].m_obj;
lean_object* v_a_2763_ = stack[2].m_obj;
lean_object* v_a_2764_ = stack[3].m_obj;
lean_object* v_a_2765_ = stack[4].m_obj;
lean_object* v_a_2766_ = stack[5].m_obj;
lean_object* v_a_2767_ = stack[6].m_obj;
lean_object* v_a_2768_ = stack[7].m_obj;
lean_object* v_res_2771_;
v_res_2771_ = l_Int_reducePow(v_e_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
stack->m_obj
 = v_res_2771_;
}
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object* v_e_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Int_reducePow(v_e_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
return v_res_2781_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2811_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2812_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2809_, v___x_2810_, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2813_;
v_res_2813_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_();
stack->m_obj
 = v_res_2813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30____boxed(lean_object* v_a_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_();
return v_res_2815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
return v___x_2817_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2820_ = 1;
v___x_2821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_);
v___x_2822_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2819_, v___x_2820_, v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2823_;
v_res_2823_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_();
stack->m_obj
 = v_res_2823_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32____boxed(lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_();
return v_res_2825_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_(){
_start:
{
lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2828_ = 1;
v___x_2829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_);
v___x_2830_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2827_, v___x_2828_, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2831_;
v_res_2831_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_();
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34____boxed(lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_();
return v_res_2833_;
}
}
lean_object* l_Int_reduceLT___redArg(lean_object* v_e_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2845_ = ((lean_object*)(l_Int_reduceLT___redArg___closed__2));
v___x_2846_ = lean_unsigned_to_nat(4u);
v___x_2847_ = l_Lean_Expr_isAppOfArity(v_e_2839_, v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v_e_2839_);
v___x_2848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = l_Lean_Expr_appFn_x21(v_e_2839_);
v___x_2851_ = l_Lean_Expr_appArg_x21(v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = l_Lean_Meta_getIntValue_x3f(v___x_2851_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2884_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2884_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2884_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 1)
{
lean_object* v_val_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_del_object(v___x_2855_);
v_val_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_val_2857_);
lean_dec_ref_known(v_a_2853_, 1);
v___x_2858_ = l_Lean_Expr_appArg_x21(v_e_2839_);
v___x_2859_ = l_Lean_Meta_getIntValue_x3f(v___x_2858_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2871_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2871_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2871_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
if (lean_obj_tag(v_a_2860_) == 1)
{
lean_object* v_val_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; 
lean_del_object(v___x_2862_);
v_val_2864_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_val_2864_);
lean_dec_ref_known(v_a_2860_, 1);
v___x_2865_ = lean_int_dec_lt(v_val_2857_, v_val_2864_);
lean_dec(v_val_2864_);
lean_dec(v_val_2857_);
v___x_2866_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2839_, v___x_2865_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
lean_dec(v_a_2860_);
lean_dec(v_val_2857_);
lean_dec_ref(v_e_2839_);
v___x_2867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2867_);
v___x_2869_ = v___x_2862_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
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
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_val_2857_);
lean_dec_ref(v_e_2839_);
v_a_2872_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2859_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2859_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
lean_dec(v_a_2853_);
lean_dec_ref(v_e_2839_);
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2880_);
v___x_2882_ = v___x_2855_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
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
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec_ref(v_e_2839_);
v_a_2885_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2852_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2852_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2839_ = stack[0].m_obj;
lean_object* v_a_2840_ = stack[1].m_obj;
lean_object* v_a_2841_ = stack[2].m_obj;
lean_object* v_a_2842_ = stack[3].m_obj;
lean_object* v_a_2843_ = stack[4].m_obj;
lean_object* v_res_2893_;
v_res_2893_ = l_Int_reduceLT___redArg(v_e_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
stack->m_obj
 = v_res_2893_;
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object* v_e_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Int_reduceLT___redArg(v_e_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2900_;
}
}
lean_object* l_Int_reduceLT(lean_object* v_e_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Int_reduceLT___redArg(v_e_2901_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2910_;
}
}
LEAN_EXPORT void l_Int_reduceLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2901_ = stack[0].m_obj;
lean_object* v_a_2902_ = stack[1].m_obj;
lean_object* v_a_2903_ = stack[2].m_obj;
lean_object* v_a_2904_ = stack[3].m_obj;
lean_object* v_a_2905_ = stack[4].m_obj;
lean_object* v_a_2906_ = stack[5].m_obj;
lean_object* v_a_2907_ = stack[6].m_obj;
lean_object* v_a_2908_ = stack[7].m_obj;
lean_object* v_res_2911_;
v_res_2911_ = l_Int_reduceLT(v_e_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
stack->m_obj
 = v_res_2911_;
}
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object* v_e_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Int_reduceLT(v_e_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
return v_res_2921_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2942_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2943_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2940_, v___x_2941_, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2944_;
v_res_2944_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2944_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27____boxed(lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_();
return v_res_2946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2951_ = 1;
v___x_2952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_);
v___x_2953_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2950_, v___x_2951_, v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2954_;
v_res_2954_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2954_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29____boxed(lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_();
return v_res_2956_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2958_; uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2959_ = 1;
v___x_2960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_);
v___x_2961_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2958_, v___x_2959_, v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2962_;
v_res_2962_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2962_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31____boxed(lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_();
return v_res_2964_;
}
}
lean_object* l_Int_reduceLE___redArg(lean_object* v_e_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = ((lean_object*)(l_Int_reduceLE___redArg___closed__2));
v___x_2977_ = lean_unsigned_to_nat(4u);
v___x_2978_ = l_Lean_Expr_isAppOfArity(v_e_2970_, v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_dec_ref(v_e_2970_);
v___x_2979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = l_Lean_Expr_appFn_x21(v_e_2970_);
v___x_2982_ = l_Lean_Expr_appArg_x21(v___x_2981_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = l_Lean_Meta_getIntValue_x3f(v___x_2982_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3015_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_3015_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3015_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
if (lean_obj_tag(v_a_2984_) == 1)
{
lean_object* v_val_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_del_object(v___x_2986_);
v_val_2988_ = lean_ctor_get(v_a_2984_, 0);
lean_inc(v_val_2988_);
lean_dec_ref_known(v_a_2984_, 1);
v___x_2989_ = l_Lean_Expr_appArg_x21(v_e_2970_);
v___x_2990_ = l_Lean_Meta_getIntValue_x3f(v___x_2989_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3002_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
if (lean_obj_tag(v_a_2991_) == 1)
{
lean_object* v_val_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; 
lean_del_object(v___x_2993_);
v_val_2995_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v_a_2991_, 1);
v___x_2996_ = lean_int_dec_le(v_val_2988_, v_val_2995_);
lean_dec(v_val_2995_);
lean_dec(v_val_2988_);
v___x_2997_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2970_, v___x_2996_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
lean_dec(v_a_2991_);
lean_dec(v_val_2988_);
lean_dec_ref(v_e_2970_);
v___x_2998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_2998_);
v___x_3000_ = v___x_2993_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_val_2988_);
lean_dec_ref(v_e_2970_);
v_a_3003_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2990_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2990_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_dec(v_a_2984_);
lean_dec_ref(v_e_2970_);
v___x_3011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_3011_);
v___x_3013_ = v___x_2986_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_e_2970_);
v_a_3016_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2983_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2983_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2970_ = stack[0].m_obj;
lean_object* v_a_2971_ = stack[1].m_obj;
lean_object* v_a_2972_ = stack[2].m_obj;
lean_object* v_a_2973_ = stack[3].m_obj;
lean_object* v_a_2974_ = stack[4].m_obj;
lean_object* v_res_3024_;
v_res_3024_ = l_Int_reduceLE___redArg(v_e_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
stack->m_obj
 = v_res_3024_;
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object* v_e_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Int_reduceLE___redArg(v_e_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3031_;
}
}
lean_object* l_Int_reduceLE(lean_object* v_e_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Int_reduceLE___redArg(v_e_3032_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT void l_Int_reduceLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3032_ = stack[0].m_obj;
lean_object* v_a_3033_ = stack[1].m_obj;
lean_object* v_a_3034_ = stack[2].m_obj;
lean_object* v_a_3035_ = stack[3].m_obj;
lean_object* v_a_3036_ = stack[4].m_obj;
lean_object* v_a_3037_ = stack[5].m_obj;
lean_object* v_a_3038_ = stack[6].m_obj;
lean_object* v_a_3039_ = stack[7].m_obj;
lean_object* v_res_3042_;
v_res_3042_ = l_Int_reduceLE(v_e_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
stack->m_obj
 = v_res_3042_;
}
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object* v_e_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Int_reduceLE(v_e_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
return v_res_3052_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3073_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_3074_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3071_, v___x_3072_, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3075_;
v_res_3075_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27____boxed(lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_();
return v_res_3077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3082_ = 1;
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_);
v___x_3084_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3081_, v___x_3082_, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3085_;
v_res_3085_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3085_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29____boxed(lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_();
return v_res_3087_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3090_ = 1;
v___x_3091_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_);
v___x_3092_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3089_, v___x_3090_, v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3093_;
v_res_3093_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3093_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31____boxed(lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_();
return v_res_3095_;
}
}
lean_object* l_Int_reduceGT___redArg(lean_object* v_e_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3107_ = ((lean_object*)(l_Int_reduceGT___redArg___closed__2));
v___x_3108_ = lean_unsigned_to_nat(4u);
v___x_3109_ = l_Lean_Expr_isAppOfArity(v_e_3101_, v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec_ref(v_e_3101_);
v___x_3110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = l_Lean_Expr_appFn_x21(v_e_3101_);
v___x_3113_ = l_Lean_Expr_appArg_x21(v___x_3112_);
lean_dec_ref(v___x_3112_);
v___x_3114_ = l_Lean_Meta_getIntValue_x3f(v___x_3113_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3146_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3146_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3146_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
if (lean_obj_tag(v_a_3115_) == 1)
{
lean_object* v_val_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_del_object(v___x_3117_);
v_val_3119_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_a_3115_, 1);
v___x_3120_ = l_Lean_Expr_appArg_x21(v_e_3101_);
v___x_3121_ = l_Lean_Meta_getIntValue_x3f(v___x_3120_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3133_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3133_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3133_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
if (lean_obj_tag(v_a_3122_) == 1)
{
lean_object* v_val_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; 
lean_del_object(v___x_3124_);
v_val_3126_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v_a_3122_, 1);
v___x_3127_ = lean_int_dec_lt(v_val_3126_, v_val_3119_);
lean_dec(v_val_3119_);
lean_dec(v_val_3126_);
v___x_3128_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3101_, v___x_3127_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_dec(v_a_3122_);
lean_dec(v_val_3119_);
lean_dec_ref(v_e_3101_);
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3129_);
v___x_3131_ = v___x_3124_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v_val_3119_);
lean_dec_ref(v_e_3101_);
v_a_3134_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3121_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3121_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_dec(v_a_3115_);
lean_dec_ref(v_e_3101_);
v___x_3142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3142_);
v___x_3144_ = v___x_3117_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v_e_3101_);
v_a_3147_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3114_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3114_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceGT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3101_ = stack[0].m_obj;
lean_object* v_a_3102_ = stack[1].m_obj;
lean_object* v_a_3103_ = stack[2].m_obj;
lean_object* v_a_3104_ = stack[3].m_obj;
lean_object* v_a_3105_ = stack[4].m_obj;
lean_object* v_res_3155_;
v_res_3155_ = l_Int_reduceGT___redArg(v_e_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
stack->m_obj
 = v_res_3155_;
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object* v_e_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Int_reduceGT___redArg(v_e_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
return v_res_3162_;
}
}
lean_object* l_Int_reduceGT(lean_object* v_e_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Int_reduceGT___redArg(v_e_3163_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT void l_Int_reduceGT_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3163_ = stack[0].m_obj;
lean_object* v_a_3164_ = stack[1].m_obj;
lean_object* v_a_3165_ = stack[2].m_obj;
lean_object* v_a_3166_ = stack[3].m_obj;
lean_object* v_a_3167_ = stack[4].m_obj;
lean_object* v_a_3168_ = stack[5].m_obj;
lean_object* v_a_3169_ = stack[6].m_obj;
lean_object* v_a_3170_ = stack[7].m_obj;
lean_object* v_res_3173_;
v_res_3173_ = l_Int_reduceGT(v_e_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
stack->m_obj
 = v_res_3173_;
}
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object* v_e_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Int_reduceGT(v_e_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
return v_res_3183_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_3191_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3192_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3189_, v___x_3190_, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3193_;
v_res_3193_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3193_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27____boxed(lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_();
return v_res_3195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3200_ = 1;
v___x_3201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_);
v___x_3202_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3199_, v___x_3200_, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3203_;
v_res_3203_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29____boxed(lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_();
return v_res_3205_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3208_ = 1;
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_);
v___x_3210_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3207_, v___x_3208_, v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3211_;
v_res_3211_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3211_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31____boxed(lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_();
return v_res_3213_;
}
}
lean_object* l_Int_reduceGE___redArg(lean_object* v_e_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3225_ = ((lean_object*)(l_Int_reduceGE___redArg___closed__2));
v___x_3226_ = lean_unsigned_to_nat(4u);
v___x_3227_ = l_Lean_Expr_isAppOfArity(v_e_3219_, v___x_3225_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_dec_ref(v_e_3219_);
v___x_3228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = l_Lean_Expr_appFn_x21(v_e_3219_);
v___x_3231_ = l_Lean_Expr_appArg_x21(v___x_3230_);
lean_dec_ref(v___x_3230_);
v___x_3232_ = l_Lean_Meta_getIntValue_x3f(v___x_3231_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3264_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3264_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3264_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
if (lean_obj_tag(v_a_3233_) == 1)
{
lean_object* v_val_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_del_object(v___x_3235_);
v_val_3237_ = lean_ctor_get(v_a_3233_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v_a_3233_, 1);
v___x_3238_ = l_Lean_Expr_appArg_x21(v_e_3219_);
v___x_3239_ = l_Lean_Meta_getIntValue_x3f(v___x_3238_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3251_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3251_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3251_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
if (lean_obj_tag(v_a_3240_) == 1)
{
lean_object* v_val_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; 
lean_del_object(v___x_3242_);
v_val_3244_ = lean_ctor_get(v_a_3240_, 0);
lean_inc(v_val_3244_);
lean_dec_ref_known(v_a_3240_, 1);
v___x_3245_ = lean_int_dec_le(v_val_3244_, v_val_3237_);
lean_dec(v_val_3237_);
lean_dec(v_val_3244_);
v___x_3246_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3219_, v___x_3245_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
lean_dec(v_a_3240_);
lean_dec(v_val_3237_);
lean_dec_ref(v_e_3219_);
v___x_3247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3247_);
v___x_3249_ = v___x_3242_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_val_3237_);
lean_dec_ref(v_e_3219_);
v_a_3252_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3239_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3239_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_dec(v_a_3233_);
lean_dec_ref(v_e_3219_);
v___x_3260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3260_);
v___x_3262_ = v___x_3235_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_e_3219_);
v_a_3265_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3232_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3232_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceGE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3219_ = stack[0].m_obj;
lean_object* v_a_3220_ = stack[1].m_obj;
lean_object* v_a_3221_ = stack[2].m_obj;
lean_object* v_a_3222_ = stack[3].m_obj;
lean_object* v_a_3223_ = stack[4].m_obj;
lean_object* v_res_3273_;
v_res_3273_ = l_Int_reduceGE___redArg(v_e_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
stack->m_obj
 = v_res_3273_;
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object* v_e_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Int_reduceGE___redArg(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
return v_res_3280_;
}
}
lean_object* l_Int_reduceGE(lean_object* v_e_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Int_reduceGE___redArg(v_e_3281_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT void l_Int_reduceGE_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3281_ = stack[0].m_obj;
lean_object* v_a_3282_ = stack[1].m_obj;
lean_object* v_a_3283_ = stack[2].m_obj;
lean_object* v_a_3284_ = stack[3].m_obj;
lean_object* v_a_3285_ = stack[4].m_obj;
lean_object* v_a_3286_ = stack[5].m_obj;
lean_object* v_a_3287_ = stack[6].m_obj;
lean_object* v_a_3288_ = stack[7].m_obj;
lean_object* v_res_3291_;
v_res_3291_ = l_Int_reduceGE(v_e_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
stack->m_obj
 = v_res_3291_;
}
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object* v_e_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Int_reduceGE(v_e_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
return v_res_3301_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3309_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3310_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3307_, v___x_3308_, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3311_;
v_res_3311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3311_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27____boxed(lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_();
return v_res_3313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3318_ = 1;
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_);
v___x_3320_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3317_, v___x_3318_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3321_;
v_res_3321_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29____boxed(lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_();
return v_res_3323_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3326_ = 1;
v___x_3327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_);
v___x_3328_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3325_, v___x_3326_, v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3329_;
v_res_3329_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31____boxed(lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_();
return v_res_3331_;
}
}
lean_object* l_Int_reduceEq___redArg(lean_object* v_e_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3341_ = ((lean_object*)(l_Int_reduceEq___redArg___closed__1));
v___x_3342_ = lean_unsigned_to_nat(3u);
v___x_3343_ = l_Lean_Expr_isAppOfArity(v_e_3335_, v___x_3341_, v___x_3342_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec_ref(v_e_3335_);
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = l_Lean_Expr_appFn_x21(v_e_3335_);
v___x_3347_ = l_Lean_Expr_appArg_x21(v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = l_Lean_Meta_getIntValue_x3f(v___x_3347_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3380_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3380_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3380_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
if (lean_obj_tag(v_a_3349_) == 1)
{
lean_object* v_val_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_del_object(v___x_3351_);
v_val_3353_ = lean_ctor_get(v_a_3349_, 0);
lean_inc(v_val_3353_);
lean_dec_ref_known(v_a_3349_, 1);
v___x_3354_ = l_Lean_Expr_appArg_x21(v_e_3335_);
v___x_3355_ = l_Lean_Meta_getIntValue_x3f(v___x_3354_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3367_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3367_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3367_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
if (lean_obj_tag(v_a_3356_) == 1)
{
lean_object* v_val_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
lean_del_object(v___x_3358_);
v_val_3360_ = lean_ctor_get(v_a_3356_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v_a_3356_, 1);
v___x_3361_ = lean_int_dec_eq(v_val_3353_, v_val_3360_);
lean_dec(v_val_3360_);
lean_dec(v_val_3353_);
v___x_3362_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3335_, v___x_3361_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
return v___x_3362_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
lean_dec(v_a_3356_);
lean_dec(v_val_3353_);
lean_dec_ref(v_e_3335_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3363_);
v___x_3365_ = v___x_3358_;
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
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v_val_3353_);
lean_dec_ref(v_e_3335_);
v_a_3368_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3355_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3355_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_dec(v_a_3349_);
lean_dec_ref(v_e_3335_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3376_);
v___x_3378_ = v___x_3351_;
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
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v_e_3335_);
v_a_3381_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3348_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3348_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3335_ = stack[0].m_obj;
lean_object* v_a_3336_ = stack[1].m_obj;
lean_object* v_a_3337_ = stack[2].m_obj;
lean_object* v_a_3338_ = stack[3].m_obj;
lean_object* v_a_3339_ = stack[4].m_obj;
lean_object* v_res_3389_;
v_res_3389_ = l_Int_reduceEq___redArg(v_e_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
stack->m_obj
 = v_res_3389_;
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object* v_e_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Int_reduceEq___redArg(v_e_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
return v_res_3396_;
}
}
lean_object* l_Int_reduceEq(lean_object* v_e_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Int_reduceEq___redArg(v_e_3397_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3406_;
}
}
LEAN_EXPORT void l_Int_reduceEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3397_ = stack[0].m_obj;
lean_object* v_a_3398_ = stack[1].m_obj;
lean_object* v_a_3399_ = stack[2].m_obj;
lean_object* v_a_3400_ = stack[3].m_obj;
lean_object* v_a_3401_ = stack[4].m_obj;
lean_object* v_a_3402_ = stack[5].m_obj;
lean_object* v_a_3403_ = stack[6].m_obj;
lean_object* v_a_3404_ = stack[7].m_obj;
lean_object* v_res_3407_;
v_res_3407_ = l_Int_reduceEq(v_e_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
stack->m_obj
 = v_res_3407_;
}
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Int_reduceEq(v_e_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
return v_res_3417_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3437_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3438_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3435_, v___x_3436_, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3439_;
v_res_3439_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3439_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27____boxed(lean_object* v_a_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_();
return v_res_3441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3446_ = 1;
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_);
v___x_3448_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3445_, v___x_3446_, v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3449_;
v_res_3449_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3449_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29____boxed(lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_();
return v_res_3451_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3454_ = 1;
v___x_3455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_);
v___x_3456_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3453_, v___x_3454_, v___x_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3457_;
v_res_3457_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3457_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31____boxed(lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_();
return v_res_3459_;
}
}
lean_object* l_Int_reduceNe___redArg(lean_object* v_e_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = ((lean_object*)(l_Int_reduceNe___redArg___closed__1));
v___x_3470_ = lean_unsigned_to_nat(3u);
v___x_3471_ = l_Lean_Expr_isAppOfArity(v_e_3463_, v___x_3469_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_dec_ref(v_e_3463_);
v___x_3472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = l_Lean_Expr_appFn_x21(v_e_3463_);
v___x_3475_ = l_Lean_Expr_appArg_x21(v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = l_Lean_Meta_getIntValue_x3f(v___x_3475_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3510_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3510_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3510_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
if (lean_obj_tag(v_a_3477_) == 1)
{
lean_object* v_val_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_del_object(v___x_3479_);
v_val_3481_ = lean_ctor_get(v_a_3477_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v_a_3477_, 1);
v___x_3482_ = l_Lean_Expr_appArg_x21(v_e_3463_);
v___x_3483_ = l_Lean_Meta_getIntValue_x3f(v___x_3482_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3497_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3497_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3497_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
if (lean_obj_tag(v_a_3484_) == 1)
{
lean_object* v_val_3488_; uint8_t v___x_3489_; 
lean_del_object(v___x_3486_);
v_val_3488_ = lean_ctor_get(v_a_3484_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v_a_3484_, 1);
v___x_3489_ = lean_int_dec_eq(v_val_3481_, v_val_3488_);
lean_dec(v_val_3488_);
lean_dec(v_val_3481_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3463_, v___x_3471_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
return v___x_3490_;
}
else
{
uint8_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = 0;
v___x_3492_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3463_, v___x_3491_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
return v___x_3492_;
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_dec(v_a_3484_);
lean_dec(v_val_3481_);
lean_dec_ref(v_e_3463_);
v___x_3493_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3493_);
v___x_3495_ = v___x_3486_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v_val_3481_);
lean_dec_ref(v_e_3463_);
v_a_3498_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3483_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3483_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_dec(v_a_3477_);
lean_dec_ref(v_e_3463_);
v___x_3506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3506_);
v___x_3508_ = v___x_3479_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref(v_e_3463_);
v_a_3511_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3476_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3476_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceNe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3463_ = stack[0].m_obj;
lean_object* v_a_3464_ = stack[1].m_obj;
lean_object* v_a_3465_ = stack[2].m_obj;
lean_object* v_a_3466_ = stack[3].m_obj;
lean_object* v_a_3467_ = stack[4].m_obj;
lean_object* v_res_3519_;
v_res_3519_ = l_Int_reduceNe___redArg(v_e_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
stack->m_obj
 = v_res_3519_;
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object* v_e_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Int_reduceNe___redArg(v_e_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
return v_res_3526_;
}
}
lean_object* l_Int_reduceNe(lean_object* v_e_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Int_reduceNe___redArg(v_e_3527_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT void l_Int_reduceNe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3527_ = stack[0].m_obj;
lean_object* v_a_3528_ = stack[1].m_obj;
lean_object* v_a_3529_ = stack[2].m_obj;
lean_object* v_a_3530_ = stack[3].m_obj;
lean_object* v_a_3531_ = stack[4].m_obj;
lean_object* v_a_3532_ = stack[5].m_obj;
lean_object* v_a_3533_ = stack[6].m_obj;
lean_object* v_a_3534_ = stack[7].m_obj;
lean_object* v_res_3537_;
v_res_3537_ = l_Int_reduceNe(v_e_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
stack->m_obj
 = v_res_3537_;
}
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object* v_e_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Int_reduceNe(v_e_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
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
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3572_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3573_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3570_, v___x_3571_, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3574_;
v_res_3574_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27____boxed(lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_();
return v_res_3576_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3581_ = 1;
v___x_3582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_);
v___x_3583_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3580_, v___x_3581_, v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3584_;
v_res_3584_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3584_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29____boxed(lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_();
return v_res_3586_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3589_ = 1;
v___x_3590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_);
v___x_3591_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3588_, v___x_3589_, v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3592_;
v_res_3592_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3592_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31____boxed(lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_();
return v_res_3594_;
}
}
lean_object* l_Int_reduceBEq___redArg(lean_object* v_e_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3606_ = ((lean_object*)(l_Int_reduceBEq___redArg___closed__2));
v___x_3607_ = lean_unsigned_to_nat(4u);
v___x_3608_ = l_Lean_Expr_isAppOfArity(v_e_3600_, v___x_3606_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = l_Lean_Expr_appFn_x21(v_e_3600_);
v___x_3612_ = l_Lean_Expr_appArg_x21(v___x_3611_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = l_Lean_Meta_getIntValue_x3f(v___x_3612_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3658_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3658_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3658_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3653_; 
v_val_3618_ = lean_ctor_get(v_a_3614_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_a_3614_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3620_ = v_a_3614_;
v_isShared_3621_ = v_isSharedCheck_3653_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_val_3618_);
lean_dec(v_a_3614_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3653_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = l_Lean_Expr_appArg_x21(v_e_3600_);
v___x_3623_ = l_Lean_Meta_getIntValue_x3f(v___x_3622_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3644_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3644_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3644_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___y_3629_; 
if (lean_obj_tag(v_a_3624_) == 1)
{
lean_object* v_val_3636_; uint8_t v___x_3637_; 
lean_del_object(v___x_3616_);
v_val_3636_ = lean_ctor_get(v_a_3624_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_a_3624_, 1);
v___x_3637_ = lean_int_dec_eq(v_val_3618_, v_val_3636_);
lean_dec(v_val_3636_);
lean_dec(v_val_3618_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
v___x_3638_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_3629_ = v___x_3638_;
goto v___jp_3628_;
}
else
{
lean_object* v___x_3639_; 
v___x_3639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_3629_ = v___x_3639_;
goto v___jp_3628_;
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3642_; 
lean_del_object(v___x_3626_);
lean_dec(v_a_3624_);
lean_del_object(v___x_3620_);
lean_dec(v_val_3618_);
v___x_3640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3640_);
v___x_3642_ = v___x_3616_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
v___jp_3628_:
{
lean_object* v___x_3631_; 
lean_inc_ref(v___y_3629_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 0);
lean_ctor_set(v___x_3620_, 0, v___y_3629_);
v___x_3631_ = v___x_3620_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___y_3629_);
v___x_3631_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3631_);
v___x_3633_ = v___x_3626_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_del_object(v___x_3620_);
lean_dec(v_val_3618_);
lean_del_object(v___x_3616_);
v_a_3645_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3623_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3623_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
lean_dec(v_a_3614_);
v___x_3654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3654_);
v___x_3656_ = v___x_3616_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
v_a_3659_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3613_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3613_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3600_ = stack[0].m_obj;
lean_object* v_a_3601_ = stack[1].m_obj;
lean_object* v_a_3602_ = stack[2].m_obj;
lean_object* v_a_3603_ = stack[3].m_obj;
lean_object* v_a_3604_ = stack[4].m_obj;
lean_object* v_res_3667_;
v_res_3667_ = l_Int_reduceBEq___redArg(v_e_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
stack->m_obj
 = v_res_3667_;
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object* v_e_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Int_reduceBEq___redArg(v_e_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_e_3668_);
return v_res_3674_;
}
}
lean_object* l_Int_reduceBEq(lean_object* v_e_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Int_reduceBEq___redArg(v_e_3675_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_);
return v___x_3684_;
}
}
LEAN_EXPORT void l_Int_reduceBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3675_ = stack[0].m_obj;
lean_object* v_a_3676_ = stack[1].m_obj;
lean_object* v_a_3677_ = stack[2].m_obj;
lean_object* v_a_3678_ = stack[3].m_obj;
lean_object* v_a_3679_ = stack[4].m_obj;
lean_object* v_a_3680_ = stack[5].m_obj;
lean_object* v_a_3681_ = stack[6].m_obj;
lean_object* v_a_3682_ = stack[7].m_obj;
lean_object* v_res_3685_;
v_res_3685_ = l_Int_reduceBEq(v_e_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_);
stack->m_obj
 = v_res_3685_;
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object* v_e_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Int_reduceBEq(v_e_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
lean_dec(v_a_3687_);
lean_dec_ref(v_e_3686_);
return v_res_3695_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3716_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3717_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3714_, v___x_3715_, v___x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3718_;
v_res_3718_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3718_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27____boxed(lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_();
return v_res_3720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3724_; uint8_t v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3725_ = 1;
v___x_3726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_);
v___x_3727_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3724_, v___x_3725_, v___x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3728_;
v_res_3728_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3728_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29____boxed(lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_();
return v_res_3730_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3733_ = 1;
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_);
v___x_3735_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3732_, v___x_3733_, v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3736_;
v_res_3736_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3736_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31____boxed(lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_();
return v_res_3738_;
}
}
lean_object* l_Int_reduceBNe___redArg(lean_object* v_e_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3748_ = ((lean_object*)(l_Int_reduceBNe___redArg___closed__1));
v___x_3749_ = lean_unsigned_to_nat(4u);
v___x_3750_ = l_Lean_Expr_isAppOfArity(v_e_3742_, v___x_3748_, v___x_3749_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
return v___x_3752_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3753_ = l_Lean_Expr_appFn_x21(v_e_3742_);
v___x_3754_ = l_Lean_Expr_appArg_x21(v___x_3753_);
lean_dec_ref(v___x_3753_);
v___x_3755_ = l_Lean_Meta_getIntValue_x3f(v___x_3754_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3801_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3801_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3801_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
if (lean_obj_tag(v_a_3756_) == 1)
{
lean_object* v_val_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3796_; 
v_val_3760_ = lean_ctor_get(v_a_3756_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_a_3756_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3762_ = v_a_3756_;
v_isShared_3763_ = v_isSharedCheck_3796_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_val_3760_);
lean_dec(v_a_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3796_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = l_Lean_Expr_appArg_x21(v_e_3742_);
v___x_3765_ = l_Lean_Meta_getIntValue_x3f(v___x_3764_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3787_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3787_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3787_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___y_3771_; 
if (lean_obj_tag(v_a_3766_) == 1)
{
lean_object* v_val_3780_; uint8_t v___x_3781_; 
lean_del_object(v___x_3758_);
v_val_3780_ = lean_ctor_get(v_a_3766_, 0);
lean_inc(v_val_3780_);
lean_dec_ref_known(v_a_3766_, 1);
v___x_3781_ = lean_int_dec_eq(v_val_3760_, v_val_3780_);
lean_dec(v_val_3780_);
lean_dec(v_val_3760_);
if (v___x_3781_ == 0)
{
if (v___x_3750_ == 0)
{
goto v___jp_3778_;
}
else
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_3771_ = v___x_3782_;
goto v___jp_3770_;
}
}
else
{
goto v___jp_3778_;
}
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_del_object(v___x_3768_);
lean_dec(v_a_3766_);
lean_del_object(v___x_3762_);
lean_dec(v_val_3760_);
v___x_3783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3783_);
v___x_3785_ = v___x_3758_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
v___jp_3770_:
{
lean_object* v___x_3773_; 
lean_inc_ref(v___y_3771_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 0);
lean_ctor_set(v___x_3762_, 0, v___y_3771_);
v___x_3773_ = v___x_3762_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___y_3771_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3773_);
v___x_3775_ = v___x_3768_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
v___jp_3778_:
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_3771_ = v___x_3779_;
goto v___jp_3770_;
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_del_object(v___x_3762_);
lean_dec(v_val_3760_);
lean_del_object(v___x_3758_);
v_a_3788_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3765_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3765_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
lean_dec(v_a_3756_);
v___x_3797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3797_);
v___x_3799_ = v___x_3758_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3755_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3755_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceBNe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3742_ = stack[0].m_obj;
lean_object* v_a_3743_ = stack[1].m_obj;
lean_object* v_a_3744_ = stack[2].m_obj;
lean_object* v_a_3745_ = stack[3].m_obj;
lean_object* v_a_3746_ = stack[4].m_obj;
lean_object* v_res_3810_;
v_res_3810_ = l_Int_reduceBNe___redArg(v_e_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
stack->m_obj
 = v_res_3810_;
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object* v_e_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Int_reduceBNe___redArg(v_e_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec_ref(v_e_3811_);
return v_res_3817_;
}
}
lean_object* l_Int_reduceBNe(lean_object* v_e_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Int_reduceBNe___redArg(v_e_3818_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT void l_Int_reduceBNe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3818_ = stack[0].m_obj;
lean_object* v_a_3819_ = stack[1].m_obj;
lean_object* v_a_3820_ = stack[2].m_obj;
lean_object* v_a_3821_ = stack[3].m_obj;
lean_object* v_a_3822_ = stack[4].m_obj;
lean_object* v_a_3823_ = stack[5].m_obj;
lean_object* v_a_3824_ = stack[6].m_obj;
lean_object* v_a_3825_ = stack[7].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l_Int_reduceBNe(v_e_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object* v_e_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Int_reduceBNe(v_e_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_a_3830_);
lean_dec_ref(v_e_3829_);
return v_res_3838_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3859_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3860_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3857_, v___x_3858_, v___x_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3861_;
v_res_3861_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_();
stack->m_obj
 = v_res_3861_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27____boxed(lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_();
return v_res_3863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
return v___x_3865_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3868_ = 1;
v___x_3869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_);
v___x_3870_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3867_, v___x_3868_, v___x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3871_;
v_res_3871_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_();
stack->m_obj
 = v_res_3871_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29____boxed(lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_();
return v_res_3873_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3876_ = 1;
v___x_3877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_);
v___x_3878_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3875_, v___x_3876_, v___x_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3879_;
v_res_3879_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3879_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31____boxed(lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_();
return v_res_3881_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(lean_object* v_declName_3882_, lean_object* v_op_3883_, lean_object* v_e_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = l_Lean_Expr_isAppOfArity(v_e_3884_, v_declName_3882_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec_ref(v_op_3883_);
v___x_3892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = l_Lean_Expr_appArg_x21(v_e_3884_);
v___x_3895_ = l_Lean_Meta_getIntValue_x3f(v___x_3894_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3917_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3917_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3917_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
if (lean_obj_tag(v_a_3896_) == 1)
{
lean_object* v_val_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3912_; 
v_val_3900_ = lean_ctor_get(v_a_3896_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_a_3896_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3902_ = v_a_3896_;
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_val_3900_);
lean_dec(v_a_3896_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3904_ = lean_apply_1(v_op_3883_, v_val_3900_);
v___x_3905_ = l_Lean_mkNatLit(v___x_3904_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3905_);
v___x_3907_ = v___x_3902_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3907_);
v___x_3909_ = v___x_3898_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_a_3896_);
lean_dec_ref(v_op_3883_);
v___x_3913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3913_);
v___x_3915_ = v___x_3898_;
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
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v_op_3883_);
v_a_3918_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3895_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3895_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3882_ = stack[0].m_obj;
lean_object* v_op_3883_ = stack[1].m_obj;
lean_object* v_e_3884_ = stack[2].m_obj;
lean_object* v_a_3885_ = stack[3].m_obj;
lean_object* v_a_3886_ = stack[4].m_obj;
lean_object* v_a_3887_ = stack[5].m_obj;
lean_object* v_a_3888_ = stack[6].m_obj;
lean_object* v_res_3926_;
v_res_3926_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(v_declName_3882_, v_op_3883_, v_e_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
stack->m_obj
 = v_res_3926_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg___boxed(lean_object* v_declName_3927_, lean_object* v_op_3928_, lean_object* v_e_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(v_declName_3927_, v_op_3928_, v_e_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec_ref(v_e_3929_);
lean_dec(v_declName_3927_);
return v_res_3935_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(lean_object* v_declName_3936_, lean_object* v_op_3937_, lean_object* v_e_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = l_Lean_Expr_isAppOfArity(v_e_3938_, v_declName_3936_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_dec_ref(v_op_3937_);
v___x_3949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = l_Lean_Expr_appArg_x21(v_e_3938_);
v___x_3952_ = l_Lean_Meta_getIntValue_x3f(v___x_3951_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3974_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3974_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3974_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
if (lean_obj_tag(v_a_3953_) == 1)
{
lean_object* v_val_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3969_; 
v_val_3957_ = lean_ctor_get(v_a_3953_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_a_3953_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3959_ = v_a_3953_;
v_isShared_3960_ = v_isSharedCheck_3969_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_val_3957_);
lean_dec(v_a_3953_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3969_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3961_ = lean_apply_1(v_op_3937_, v_val_3957_);
v___x_3962_ = l_Lean_mkNatLit(v___x_3961_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3962_);
v___x_3964_ = v___x_3959_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3966_; 
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
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3972_; 
lean_dec(v_a_3953_);
lean_dec_ref(v_op_3937_);
v___x_3970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_3970_);
v___x_3972_ = v___x_3955_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec_ref(v_op_3937_);
v_a_3975_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3952_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3952_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3936_ = stack[0].m_obj;
lean_object* v_op_3937_ = stack[1].m_obj;
lean_object* v_e_3938_ = stack[2].m_obj;
lean_object* v_a_3939_ = stack[3].m_obj;
lean_object* v_a_3940_ = stack[4].m_obj;
lean_object* v_a_3941_ = stack[5].m_obj;
lean_object* v_a_3942_ = stack[6].m_obj;
lean_object* v_a_3943_ = stack[7].m_obj;
lean_object* v_a_3944_ = stack[8].m_obj;
lean_object* v_a_3945_ = stack[9].m_obj;
lean_object* v_res_3983_;
v_res_3983_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(v_declName_3936_, v_op_3937_, v_e_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
stack->m_obj
 = v_res_3983_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___boxed(lean_object* v_declName_3984_, lean_object* v_op_3985_, lean_object* v_e_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(v_declName_3984_, v_op_3985_, v_e_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_e_3986_);
lean_dec(v_declName_3984_);
return v_res_3995_;
}
}
lean_object* l_Int_reduceAbs___redArg(lean_object* v_e_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = ((lean_object*)(l_Int_reduceAbs___redArg___closed__1));
v___x_4007_ = lean_unsigned_to_nat(1u);
v___x_4008_ = l_Lean_Expr_isAppOfArity(v_e_4000_, v___x_4006_, v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = l_Lean_Expr_appArg_x21(v_e_4000_);
v___x_4012_ = l_Lean_Meta_getIntValue_x3f(v___x_4011_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4034_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4034_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4034_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
if (lean_obj_tag(v_a_4013_) == 1)
{
lean_object* v_val_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4029_; 
v_val_4017_ = lean_ctor_get(v_a_4013_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_a_4013_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4019_ = v_a_4013_;
v_isShared_4020_ = v_isSharedCheck_4029_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_val_4017_);
lean_dec(v_a_4013_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4029_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4021_ = lean_nat_abs(v_val_4017_);
lean_dec(v_val_4017_);
v___x_4022_ = l_Lean_mkNatLit(v___x_4021_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set_tag(v___x_4019_, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4026_; 
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4024_);
v___x_4026_ = v___x_4015_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
lean_dec(v_a_4013_);
v___x_4030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4030_);
v___x_4032_ = v___x_4015_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4012_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4012_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceAbs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4000_ = stack[0].m_obj;
lean_object* v_a_4001_ = stack[1].m_obj;
lean_object* v_a_4002_ = stack[2].m_obj;
lean_object* v_a_4003_ = stack[3].m_obj;
lean_object* v_a_4004_ = stack[4].m_obj;
lean_object* v_res_4043_;
v_res_4043_ = l_Int_reduceAbs___redArg(v_e_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
stack->m_obj
 = v_res_4043_;
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object* v_e_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Int_reduceAbs___redArg(v_e_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
lean_dec_ref(v_e_4044_);
return v_res_4050_;
}
}
lean_object* l_Int_reduceAbs(lean_object* v_e_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Int_reduceAbs___redArg(v_e_4051_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT void l_Int_reduceAbs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4051_ = stack[0].m_obj;
lean_object* v_a_4052_ = stack[1].m_obj;
lean_object* v_a_4053_ = stack[2].m_obj;
lean_object* v_a_4054_ = stack[3].m_obj;
lean_object* v_a_4055_ = stack[4].m_obj;
lean_object* v_a_4056_ = stack[5].m_obj;
lean_object* v_a_4057_ = stack[6].m_obj;
lean_object* v_a_4058_ = stack[7].m_obj;
lean_object* v_res_4061_;
v_res_4061_ = l_Int_reduceAbs(v_e_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
stack->m_obj
 = v_res_4061_;
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object* v_e_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Int_reduceAbs(v_e_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_e_4062_);
return v_res_4071_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_4087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_4088_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_4089_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4086_, v___x_4087_, v___x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4090_;
v_res_4090_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_();
stack->m_obj
 = v_res_4090_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20____boxed(lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_();
return v_res_4092_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4093_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
return v___x_4094_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_4097_ = 1;
v___x_4098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_);
v___x_4099_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4096_, v___x_4097_, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4100_;
v_res_4100_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_();
stack->m_obj
 = v_res_4100_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22____boxed(lean_object* v_a_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_();
return v_res_4102_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4104_; uint8_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_4105_ = 1;
v___x_4106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_);
v___x_4107_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4104_, v___x_4105_, v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4108_;
v_res_4108_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_();
stack->m_obj
 = v_res_4108_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24____boxed(lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_();
return v_res_4110_;
}
}
lean_object* l_Int_reduceToNat___redArg(lean_object* v_e_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; 
v___x_4121_ = ((lean_object*)(l_Int_reduceToNat___redArg___closed__1));
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = l_Lean_Expr_isAppOfArity(v_e_4115_, v___x_4121_, v___x_4122_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = l_Lean_Expr_appArg_x21(v_e_4115_);
v___x_4127_ = l_Lean_Meta_getIntValue_x3f(v___x_4126_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4149_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4149_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4149_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
if (lean_obj_tag(v_a_4128_) == 1)
{
lean_object* v_val_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4144_; 
v_val_4132_ = lean_ctor_get(v_a_4128_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_a_4128_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4134_ = v_a_4128_;
v_isShared_4135_ = v_isSharedCheck_4144_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_val_4132_);
lean_dec(v_a_4128_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4144_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4136_ = l_Int_toNat(v_val_4132_);
lean_dec(v_val_4132_);
v___x_4137_ = l_Lean_mkNatLit(v___x_4136_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4137_);
v___x_4139_ = v___x_4134_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4141_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4139_);
v___x_4141_ = v___x_4130_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
lean_dec(v_a_4128_);
v___x_4145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4145_);
v___x_4147_ = v___x_4130_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
v_a_4150_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4127_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4127_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_reduceToNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4115_ = stack[0].m_obj;
lean_object* v_a_4116_ = stack[1].m_obj;
lean_object* v_a_4117_ = stack[2].m_obj;
lean_object* v_a_4118_ = stack[3].m_obj;
lean_object* v_a_4119_ = stack[4].m_obj;
lean_object* v_res_4158_;
v_res_4158_ = l_Int_reduceToNat___redArg(v_e_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
stack->m_obj
 = v_res_4158_;
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object* v_e_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Int_reduceToNat___redArg(v_e_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec_ref(v_e_4159_);
return v_res_4165_;
}
}
lean_object* l_Int_reduceToNat(lean_object* v_e_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Int_reduceToNat___redArg(v_e_4166_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
return v___x_4175_;
}
}
LEAN_EXPORT void l_Int_reduceToNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4166_ = stack[0].m_obj;
lean_object* v_a_4167_ = stack[1].m_obj;
lean_object* v_a_4168_ = stack[2].m_obj;
lean_object* v_a_4169_ = stack[3].m_obj;
lean_object* v_a_4170_ = stack[4].m_obj;
lean_object* v_a_4171_ = stack[5].m_obj;
lean_object* v_a_4172_ = stack[6].m_obj;
lean_object* v_a_4173_ = stack[7].m_obj;
lean_object* v_res_4176_;
v_res_4176_ = l_Int_reduceToNat(v_e_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
stack->m_obj
 = v_res_4176_;
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object* v_e_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Int_reduceToNat(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_e_4177_);
return v_res_4186_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4203_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4204_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4201_, v___x_4202_, v___x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4205_;
v_res_4205_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_();
stack->m_obj
 = v_res_4205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20____boxed(lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_();
return v_res_4207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4211_; uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4212_ = 1;
v___x_4213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_);
v___x_4214_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4211_, v___x_4212_, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4215_;
v_res_4215_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_();
stack->m_obj
 = v_res_4215_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22____boxed(lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_();
return v_res_4217_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4219_; uint8_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4220_ = 1;
v___x_4221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_);
v___x_4222_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4219_, v___x_4220_, v___x_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4223_;
v_res_4223_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_();
stack->m_obj
 = v_res_4223_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24____boxed(lean_object* v_a_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_();
return v_res_4225_;
}
}
static lean_object* _init_l_Int_reduceNegSucc___redArg___closed__2(void){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_unsigned_to_nat(1u);
v___x_4231_ = lean_nat_to_int(v___x_4230_);
return v___x_4231_;
}
}
lean_object* l_Int_reduceNegSucc___redArg(lean_object* v_e_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4232_, v_a_4234_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4292_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4292_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4292_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; uint8_t v___x_4247_; 
v___x_4246_ = l_Lean_Expr_cleanupAnnotations(v_a_4242_);
v___x_4247_ = l_Lean_Expr_isApp(v___x_4246_);
if (v___x_4247_ == 0)
{
lean_dec_ref(v___x_4246_);
lean_del_object(v___x_4244_);
goto v___jp_4238_;
}
else
{
lean_object* v_arg_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v_arg_4248_ = lean_ctor_get(v___x_4246_, 1);
lean_inc_ref(v_arg_4248_);
v___x_4249_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4246_);
v___x_4250_ = ((lean_object*)(l_Int_reduceNegSucc___redArg___closed__1));
v___x_4251_ = l_Lean_Expr_isConstOf(v___x_4249_, v___x_4250_);
lean_dec_ref(v___x_4249_);
if (v___x_4251_ == 0)
{
lean_dec_ref(v_arg_4248_);
lean_del_object(v___x_4244_);
goto v___jp_4238_;
}
else
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_getNatValue_x3f(v_arg_4248_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
lean_dec_ref(v_arg_4248_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4283_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4283_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4283_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___y_4258_; 
if (lean_obj_tag(v_a_4253_) == 1)
{
lean_object* v_val_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
lean_del_object(v___x_4244_);
v_val_4263_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_val_4263_);
lean_dec_ref_known(v_a_4253_, 1);
v___x_4264_ = lean_nat_to_int(v_val_4263_);
v___x_4265_ = lean_obj_once(&l_Int_reduceNegSucc___redArg___closed__2, &l_Int_reduceNegSucc___redArg___closed__2_once, _init_l_Int_reduceNegSucc___redArg___closed__2);
v___x_4266_ = lean_int_add(v___x_4264_, v___x_4265_);
lean_dec(v___x_4264_);
v___x_4267_ = lean_int_neg(v___x_4266_);
lean_dec(v___x_4266_);
v___x_4268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4269_ = lean_int_dec_le(v___x_4268_, v___x_4267_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4273_ = lean_int_neg(v___x_4267_);
lean_dec(v___x_4267_);
v___x_4274_ = l_Int_toNat(v___x_4273_);
lean_dec(v___x_4273_);
v___x_4275_ = l_Lean_instToExprInt_mkNat(v___x_4274_);
v___x_4276_ = l_Lean_mkApp3(v___x_4270_, v___x_4271_, v___x_4272_, v___x_4275_);
v___y_4258_ = v___x_4276_;
goto v___jp_4257_;
}
else
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = l_Int_toNat(v___x_4267_);
lean_dec(v___x_4267_);
v___x_4278_ = l_Lean_instToExprInt_mkNat(v___x_4277_);
v___y_4258_ = v___x_4278_;
goto v___jp_4257_;
}
}
else
{
lean_object* v___x_4279_; lean_object* v___x_4281_; 
lean_del_object(v___x_4255_);
lean_dec(v_a_4253_);
v___x_4279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4279_);
v___x_4281_ = v___x_4244_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
v___jp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___y_4258_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4259_);
v___x_4261_ = v___x_4255_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_del_object(v___x_4244_);
v_a_4284_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4252_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4252_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
v_a_4293_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4241_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4241_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
v___jp_4238_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
}
}
LEAN_EXPORT void l_Int_reduceNegSucc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4232_ = stack[0].m_obj;
lean_object* v_a_4233_ = stack[1].m_obj;
lean_object* v_a_4234_ = stack[2].m_obj;
lean_object* v_a_4235_ = stack[3].m_obj;
lean_object* v_a_4236_ = stack[4].m_obj;
lean_object* v_res_4301_;
v_res_4301_ = l_Int_reduceNegSucc___redArg(v_e_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
stack->m_obj
 = v_res_4301_;
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object* v_e_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Int_reduceNegSucc___redArg(v_e_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
return v_res_4308_;
}
}
lean_object* l_Int_reduceNegSucc(lean_object* v_e_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Int_reduceNegSucc___redArg(v_e_4309_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT void l_Int_reduceNegSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4309_ = stack[0].m_obj;
lean_object* v_a_4310_ = stack[1].m_obj;
lean_object* v_a_4311_ = stack[2].m_obj;
lean_object* v_a_4312_ = stack[3].m_obj;
lean_object* v_a_4313_ = stack[4].m_obj;
lean_object* v_a_4314_ = stack[5].m_obj;
lean_object* v_a_4315_ = stack[6].m_obj;
lean_object* v_a_4316_ = stack[7].m_obj;
lean_object* v_res_4319_;
v_res_4319_ = l_Int_reduceNegSucc(v_e_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
stack->m_obj
 = v_res_4319_;
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object* v_e_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Int_reduceNegSucc(v_e_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
return v_res_4329_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4346_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4347_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4344_, v___x_4345_, v___x_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4348_;
v_res_4348_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_();
stack->m_obj
 = v_res_4348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20____boxed(lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_();
return v_res_4350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4355_ = 1;
v___x_4356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_);
v___x_4357_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4354_, v___x_4355_, v___x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4358_;
v_res_4358_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_();
stack->m_obj
 = v_res_4358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22____boxed(lean_object* v_a_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_();
return v_res_4360_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4362_; uint8_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4363_ = 1;
v___x_4364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_);
v___x_4365_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4362_, v___x_4363_, v___x_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4366_;
v_res_4366_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_();
stack->m_obj
 = v_res_4366_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24____boxed(lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_();
return v_res_4368_;
}
}
lean_object* l_Int_reduceOfNat___redArg(lean_object* v_e_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4372_, v_a_4374_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4429_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4429_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4429_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4386_ = l_Lean_Expr_cleanupAnnotations(v_a_4382_);
v___x_4387_ = l_Lean_Expr_isApp(v___x_4386_);
if (v___x_4387_ == 0)
{
lean_dec_ref(v___x_4386_);
lean_del_object(v___x_4384_);
goto v___jp_4378_;
}
else
{
lean_object* v_arg_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v_arg_4388_ = lean_ctor_get(v___x_4386_, 1);
lean_inc_ref(v_arg_4388_);
v___x_4389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4386_);
v___x_4390_ = ((lean_object*)(l_Int_reduceOfNat___redArg___closed__0));
v___x_4391_ = l_Lean_Expr_isConstOf(v___x_4389_, v___x_4390_);
lean_dec_ref(v___x_4389_);
if (v___x_4391_ == 0)
{
lean_dec_ref(v_arg_4388_);
lean_del_object(v___x_4384_);
goto v___jp_4378_;
}
else
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_Meta_getNatValue_x3f(v_arg_4388_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
lean_dec_ref(v_arg_4388_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4420_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4395_ = v___x_4392_;
v_isShared_4396_ = v_isSharedCheck_4420_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4420_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___y_4398_; 
if (lean_obj_tag(v_a_4393_) == 1)
{
lean_object* v_val_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; 
lean_del_object(v___x_4384_);
v_val_4403_ = lean_ctor_get(v_a_4393_, 0);
lean_inc(v_val_4403_);
lean_dec_ref_known(v_a_4393_, 1);
v___x_4404_ = lean_nat_to_int(v_val_4403_);
v___x_4405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4406_ = lean_int_dec_le(v___x_4405_, v___x_4404_);
if (v___x_4406_ == 0)
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4410_ = lean_int_neg(v___x_4404_);
lean_dec(v___x_4404_);
v___x_4411_ = l_Int_toNat(v___x_4410_);
lean_dec(v___x_4410_);
v___x_4412_ = l_Lean_instToExprInt_mkNat(v___x_4411_);
v___x_4413_ = l_Lean_mkApp3(v___x_4407_, v___x_4408_, v___x_4409_, v___x_4412_);
v___y_4398_ = v___x_4413_;
goto v___jp_4397_;
}
else
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = l_Int_toNat(v___x_4404_);
lean_dec(v___x_4404_);
v___x_4415_ = l_Lean_instToExprInt_mkNat(v___x_4414_);
v___y_4398_ = v___x_4415_;
goto v___jp_4397_;
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
lean_del_object(v___x_4395_);
lean_dec(v_a_4393_);
v___x_4416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 0, v___x_4416_);
v___x_4418_ = v___x_4384_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
v___jp_4397_:
{
lean_object* v___x_4399_; lean_object* v___x_4401_; 
v___x_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4399_, 0, v___y_4398_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4399_);
v___x_4401_ = v___x_4395_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4399_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_del_object(v___x_4384_);
v_a_4421_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4392_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4392_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_a_4430_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4381_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4381_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
v___jp_4378_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
return v___x_4380_;
}
}
}
LEAN_EXPORT void l_Int_reduceOfNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4372_ = stack[0].m_obj;
lean_object* v_a_4373_ = stack[1].m_obj;
lean_object* v_a_4374_ = stack[2].m_obj;
lean_object* v_a_4375_ = stack[3].m_obj;
lean_object* v_a_4376_ = stack[4].m_obj;
lean_object* v_res_4438_;
v_res_4438_ = l_Int_reduceOfNat___redArg(v_e_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
stack->m_obj
 = v_res_4438_;
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object* v_e_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Int_reduceOfNat___redArg(v_e_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
return v_res_4445_;
}
}
lean_object* l_Int_reduceOfNat(lean_object* v_e_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_Int_reduceOfNat___redArg(v_e_4446_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4455_;
}
}
LEAN_EXPORT void l_Int_reduceOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4446_ = stack[0].m_obj;
lean_object* v_a_4447_ = stack[1].m_obj;
lean_object* v_a_4448_ = stack[2].m_obj;
lean_object* v_a_4449_ = stack[3].m_obj;
lean_object* v_a_4450_ = stack[4].m_obj;
lean_object* v_a_4451_ = stack[5].m_obj;
lean_object* v_a_4452_ = stack[6].m_obj;
lean_object* v_a_4453_ = stack[7].m_obj;
lean_object* v_res_4456_;
v_res_4456_ = l_Int_reduceOfNat(v_e_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
stack->m_obj
 = v_res_4456_;
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object* v_e_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Int_reduceOfNat(v_e_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
lean_dec(v_a_4458_);
return v_res_4466_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4483_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4484_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4481_, v___x_4482_, v___x_4483_);
return v___x_4484_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4485_;
v_res_4485_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_();
stack->m_obj
 = v_res_4485_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20____boxed(lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_();
return v_res_4487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
return v___x_4489_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4491_; uint8_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4492_ = 1;
v___x_4493_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_);
v___x_4494_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4491_, v___x_4492_, v___x_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4495_;
v_res_4495_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_();
stack->m_obj
 = v_res_4495_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22____boxed(lean_object* v_a_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_();
return v_res_4497_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4499_; uint8_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4500_ = 1;
v___x_4501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_);
v___x_4502_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4499_, v___x_4500_, v___x_4501_);
return v___x_4502_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4503_;
v_res_4503_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_();
stack->m_obj
 = v_res_4503_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24____boxed(lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_();
return v_res_4505_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = lean_box(0);
v___x_4516_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__4));
v___x_4517_ = l_Lean_mkConst(v___x_4516_, v___x_4515_);
return v___x_4517_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = lean_box(0);
v___x_4522_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__7));
v___x_4523_ = l_Lean_mkConst(v___x_4522_, v___x_4521_);
return v___x_4523_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4528_ = lean_box(0);
v___x_4529_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__10));
v___x_4530_ = l_Lean_mkConst(v___x_4529_, v___x_4528_);
return v___x_4530_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__14(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = lean_box(0);
v___x_4535_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__13));
v___x_4536_ = l_Lean_mkConst(v___x_4535_, v___x_4534_);
return v___x_4536_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__17(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4541_ = lean_box(0);
v___x_4542_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__16));
v___x_4543_ = l_Lean_mkConst(v___x_4542_, v___x_4541_);
return v___x_4543_;
}
}
lean_object* l_Int_reduceDvd___redArg(lean_object* v_e_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4544_, v_a_4546_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4553_, 1);
v___x_4555_ = l_Lean_Expr_cleanupAnnotations(v_a_4554_);
v___x_4556_ = l_Lean_Expr_isApp(v___x_4555_);
if (v___x_4556_ == 0)
{
lean_dec_ref(v___x_4555_);
goto v___jp_4550_;
}
else
{
lean_object* v_arg_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; 
v_arg_4557_ = lean_ctor_get(v___x_4555_, 1);
lean_inc_ref(v_arg_4557_);
v___x_4558_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4555_);
v___x_4559_ = l_Lean_Expr_isApp(v___x_4558_);
if (v___x_4559_ == 0)
{
lean_dec_ref(v___x_4558_);
lean_dec_ref(v_arg_4557_);
goto v___jp_4550_;
}
else
{
lean_object* v_arg_4560_; lean_object* v___x_4561_; uint8_t v___x_4562_; 
v_arg_4560_ = lean_ctor_get(v___x_4558_, 1);
lean_inc_ref(v_arg_4560_);
v___x_4561_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4558_);
v___x_4562_ = l_Lean_Expr_isApp(v___x_4561_);
if (v___x_4562_ == 0)
{
lean_dec_ref(v___x_4561_);
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
goto v___jp_4550_;
}
else
{
lean_object* v_arg_4563_; lean_object* v___x_4564_; uint8_t v___x_4565_; 
v_arg_4563_ = lean_ctor_get(v___x_4561_, 1);
lean_inc_ref(v_arg_4563_);
v___x_4564_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4561_);
v___x_4565_ = l_Lean_Expr_isApp(v___x_4564_);
if (v___x_4565_ == 0)
{
lean_dec_ref(v___x_4564_);
lean_dec_ref(v_arg_4563_);
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
goto v___jp_4550_;
}
else
{
lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v___x_4566_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4564_);
v___x_4567_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__2));
v___x_4568_ = l_Lean_Expr_isConstOf(v___x_4566_, v___x_4567_);
lean_dec_ref(v___x_4566_);
if (v___x_4568_ == 0)
{
lean_dec_ref(v_arg_4563_);
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
goto v___jp_4550_;
}
else
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__5, &l_Int_reduceDvd___redArg___closed__5_once, _init_l_Int_reduceDvd___redArg___closed__5);
v___x_4570_ = l_Lean_Meta_matchesInstance(v_arg_4563_, v___x_4569_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4657_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4657_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4657_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
uint8_t v___x_4575_; 
v___x_4575_ = lean_unbox(v_a_4571_);
lean_dec(v_a_4571_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4578_; 
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
v___x_4576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v___x_4576_);
v___x_4578_ = v___x_4573_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
else
{
lean_object* v___x_4580_; 
lean_del_object(v___x_4573_);
lean_inc_ref(v_arg_4560_);
v___x_4580_ = l_Lean_Meta_getIntValue_x3f(v_arg_4560_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4648_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4648_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4648_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
if (lean_obj_tag(v_a_4581_) == 1)
{
lean_object* v_val_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4643_; 
lean_del_object(v___x_4583_);
v_val_4585_ = lean_ctor_get(v_a_4581_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_a_4581_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4587_ = v_a_4581_;
v_isShared_4588_ = v_isSharedCheck_4643_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_val_4585_);
lean_dec(v_a_4581_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4643_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; 
lean_inc_ref(v_arg_4557_);
v___x_4589_ = l_Lean_Meta_getIntValue_x3f(v_arg_4557_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4634_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4634_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4634_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
if (lean_obj_tag(v_a_4590_) == 1)
{
lean_object* v_val_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4629_; 
v_val_4594_ = lean_ctor_get(v_a_4590_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_a_4590_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4596_ = v_a_4590_;
v_isShared_4597_ = v_isSharedCheck_4629_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_val_4594_);
lean_dec(v_a_4590_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4629_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; 
v___x_4598_ = lean_int_emod(v_val_4594_, v_val_4585_);
lean_dec(v_val_4585_);
lean_dec(v_val_4594_);
v___x_4599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4600_ = lean_int_dec_eq(v___x_4598_, v___x_4599_);
lean_dec(v___x_4598_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4601_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__8, &l_Int_reduceDvd___redArg___closed__8_once, _init_l_Int_reduceDvd___redArg___closed__8);
v___x_4602_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__11, &l_Int_reduceDvd___redArg___closed__11_once, _init_l_Int_reduceDvd___redArg___closed__11);
v___x_4603_ = l_Lean_eagerReflBoolTrue;
v___x_4604_ = l_Lean_mkApp3(v___x_4602_, v_arg_4560_, v_arg_4557_, v___x_4603_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4604_);
v___x_4606_ = v___x_4596_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4607_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4607_, 0, v___x_4601_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
lean_ctor_set_uint8(v___x_4607_, sizeof(void*)*2, v___x_4568_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set_tag(v___x_4587_, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4607_);
v___x_4609_ = v___x_4587_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4611_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4609_);
v___x_4611_ = v___x_4592_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4615_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__14, &l_Int_reduceDvd___redArg___closed__14_once, _init_l_Int_reduceDvd___redArg___closed__14);
v___x_4616_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__17, &l_Int_reduceDvd___redArg___closed__17_once, _init_l_Int_reduceDvd___redArg___closed__17);
v___x_4617_ = l_Lean_eagerReflBoolTrue;
v___x_4618_ = l_Lean_mkApp3(v___x_4616_, v_arg_4560_, v_arg_4557_, v___x_4617_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4618_);
v___x_4620_ = v___x_4596_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4621_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4621_, 0, v___x_4615_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
lean_ctor_set_uint8(v___x_4621_, sizeof(void*)*2, v___x_4568_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set_tag(v___x_4587_, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4621_);
v___x_4623_ = v___x_4587_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4625_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4623_);
v___x_4625_ = v___x_4592_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4632_; 
lean_dec(v_a_4590_);
lean_del_object(v___x_4587_);
lean_dec(v_val_4585_);
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
v___x_4630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4630_);
v___x_4632_ = v___x_4592_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_del_object(v___x_4587_);
lean_dec(v_val_4585_);
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
v_a_4635_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4589_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4589_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4646_; 
lean_dec(v_a_4581_);
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
v___x_4644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4644_);
v___x_4646_ = v___x_4583_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4644_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
v_a_4649_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4580_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4580_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_dec_ref(v_arg_4560_);
lean_dec_ref(v_arg_4557_);
v_a_4658_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4570_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4570_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
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
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
v_a_4666_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4553_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4553_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
v___jp_4550_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
return v___x_4552_;
}
}
}
LEAN_EXPORT void l_Int_reduceDvd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4544_ = stack[0].m_obj;
lean_object* v_a_4545_ = stack[1].m_obj;
lean_object* v_a_4546_ = stack[2].m_obj;
lean_object* v_a_4547_ = stack[3].m_obj;
lean_object* v_a_4548_ = stack[4].m_obj;
lean_object* v_res_4674_;
v_res_4674_ = l_Int_reduceDvd___redArg(v_e_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
stack->m_obj
 = v_res_4674_;
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object* v_e_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l_Int_reduceDvd___redArg(v_e_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4681_;
}
}
lean_object* l_Int_reduceDvd(lean_object* v_e_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_Int_reduceDvd___redArg(v_e_4682_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
return v___x_4691_;
}
}
LEAN_EXPORT void l_Int_reduceDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4682_ = stack[0].m_obj;
lean_object* v_a_4683_ = stack[1].m_obj;
lean_object* v_a_4684_ = stack[2].m_obj;
lean_object* v_a_4685_ = stack[3].m_obj;
lean_object* v_a_4686_ = stack[4].m_obj;
lean_object* v_a_4687_ = stack[5].m_obj;
lean_object* v_a_4688_ = stack[6].m_obj;
lean_object* v_a_4689_ = stack[7].m_obj;
lean_object* v_res_4692_;
v_res_4692_ = l_Int_reduceDvd(v_e_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
stack->m_obj
 = v_res_4692_;
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object* v_e_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Int_reduceDvd(v_e_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
return v_res_4702_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4723_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4724_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4721_, v___x_4722_, v___x_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4725_;
v_res_4725_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_();
stack->m_obj
 = v_res_4725_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26____boxed(lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_();
return v_res_4727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
return v___x_4729_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_4731_; uint8_t v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
v___x_4731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4732_ = 1;
v___x_4733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_);
v___x_4734_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4731_, v___x_4732_, v___x_4733_);
return v___x_4734_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4735_;
v_res_4735_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_();
stack->m_obj
 = v_res_4735_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28____boxed(lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_();
return v_res_4737_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4740_ = 1;
v___x_4741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_);
v___x_4742_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4739_, v___x_4740_, v___x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4743_;
v_res_4743_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_();
stack->m_obj
 = v_res_4743_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30____boxed(lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_();
return v_res_4745_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object* v_inst_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Lean_Meta_getNatValue_x3f(v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4811_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4811_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4811_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
if (lean_obj_tag(v_a_4757_) == 1)
{
lean_object* v_val_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4806_; 
v_val_4761_ = lean_ctor_get(v_a_4757_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_a_4757_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4763_ = v_a_4757_;
v_isShared_4764_ = v_isSharedCheck_4806_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_val_4761_);
lean_dec(v_a_4757_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4806_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_4749_, v_a_4752_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4797_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4768_ = v___x_4765_;
v_isShared_4769_ = v_isSharedCheck_4797_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4765_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4797_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___y_4771_; lean_object* v___x_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; 
v___x_4778_ = l_Lean_Expr_cleanupAnnotations(v_a_4766_);
v___x_4779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1));
v___x_4780_ = l_Lean_Expr_isConstOf(v___x_4778_, v___x_4779_);
lean_dec_ref(v___x_4778_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; lean_object* v___x_4783_; 
lean_del_object(v___x_4768_);
lean_del_object(v___x_4763_);
lean_dec(v_val_4761_);
v___x_4781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4781_);
v___x_4783_ = v___x_4759_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
else
{
lean_object* v___x_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
lean_del_object(v___x_4759_);
v___x_4785_ = lean_nat_to_int(v_val_4761_);
v___x_4786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4787_ = lean_int_dec_le(v___x_4786_, v___x_4785_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4791_ = lean_int_neg(v___x_4785_);
lean_dec(v___x_4785_);
v___x_4792_ = l_Int_toNat(v___x_4791_);
lean_dec(v___x_4791_);
v___x_4793_ = l_Lean_instToExprInt_mkNat(v___x_4792_);
v___x_4794_ = l_Lean_mkApp3(v___x_4788_, v___x_4789_, v___x_4790_, v___x_4793_);
v___y_4771_ = v___x_4794_;
goto v___jp_4770_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = l_Int_toNat(v___x_4785_);
lean_dec(v___x_4785_);
v___x_4796_ = l_Lean_instToExprInt_mkNat(v___x_4795_);
v___y_4771_ = v___x_4796_;
goto v___jp_4770_;
}
}
v___jp_4770_:
{
lean_object* v___x_4773_; 
if (v_isShared_4764_ == 0)
{
lean_ctor_set_tag(v___x_4763_, 0);
lean_ctor_set(v___x_4763_, 0, v___y_4771_);
v___x_4773_ = v___x_4763_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___y_4771_);
v___x_4773_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
lean_object* v___x_4775_; 
if (v_isShared_4769_ == 0)
{
lean_ctor_set(v___x_4768_, 0, v___x_4773_);
v___x_4775_ = v___x_4768_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_del_object(v___x_4763_);
lean_dec(v_val_4761_);
lean_del_object(v___x_4759_);
v_a_4798_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4765_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4765_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4809_; 
lean_dec(v_a_4757_);
lean_dec_ref(v_inst_4749_);
v___x_4807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4807_);
v___x_4809_ = v___x_4759_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_dec_ref(v_inst_4749_);
v_a_4812_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4756_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4756_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4749_ = stack[0].m_obj;
lean_object* v_a_4750_ = stack[1].m_obj;
lean_object* v_a_4751_ = stack[2].m_obj;
lean_object* v_a_4752_ = stack[3].m_obj;
lean_object* v_a_4753_ = stack[4].m_obj;
lean_object* v_a_4754_ = stack[5].m_obj;
lean_object* v_res_4820_;
v_res_4820_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
stack->m_obj
 = v_res_4820_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object* v_inst_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
lean_dec_ref(v_a_4822_);
return v_res_4828_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object* v_inst_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4829_, v_a_4830_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
return v___x_4839_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4829_ = stack[0].m_obj;
lean_object* v_a_4830_ = stack[1].m_obj;
lean_object* v_a_4831_ = stack[2].m_obj;
lean_object* v_a_4832_ = stack[3].m_obj;
lean_object* v_a_4833_ = stack[4].m_obj;
lean_object* v_a_4834_ = stack[5].m_obj;
lean_object* v_a_4835_ = stack[6].m_obj;
lean_object* v_a_4836_ = stack[7].m_obj;
lean_object* v_a_4837_ = stack[8].m_obj;
lean_object* v_res_4840_;
v_res_4840_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(v_inst_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
stack->m_obj
 = v_res_4840_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object* v_inst_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(v_inst_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
return v_res_4851_;
}
}
lean_object* l_Int_reduceNatCast___redArg(lean_object* v_e_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4857_, v_a_4859_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; uint8_t v___x_4869_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v___x_4868_ = l_Lean_Expr_cleanupAnnotations(v_a_4867_);
v___x_4869_ = l_Lean_Expr_isApp(v___x_4868_);
if (v___x_4869_ == 0)
{
lean_dec_ref(v___x_4868_);
goto v___jp_4863_;
}
else
{
lean_object* v_arg_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; 
v_arg_4870_ = lean_ctor_get(v___x_4868_, 1);
lean_inc_ref(v_arg_4870_);
v___x_4871_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4868_);
v___x_4872_ = l_Lean_Expr_isApp(v___x_4871_);
if (v___x_4872_ == 0)
{
lean_dec_ref(v___x_4871_);
lean_dec_ref(v_arg_4870_);
goto v___jp_4863_;
}
else
{
lean_object* v_arg_4873_; lean_object* v___x_4874_; uint8_t v___x_4875_; 
v_arg_4873_ = lean_ctor_get(v___x_4871_, 1);
lean_inc_ref(v_arg_4873_);
v___x_4874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4871_);
v___x_4875_ = l_Lean_Expr_isApp(v___x_4874_);
if (v___x_4875_ == 0)
{
lean_dec_ref(v___x_4874_);
lean_dec_ref(v_arg_4873_);
lean_dec_ref(v_arg_4870_);
goto v___jp_4863_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4876_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4874_);
v___x_4877_ = ((lean_object*)(l_Int_reduceNatCast___redArg___closed__2));
v___x_4878_ = l_Lean_Expr_isConstOf(v___x_4876_, v___x_4877_);
lean_dec_ref(v___x_4876_);
if (v___x_4878_ == 0)
{
lean_dec_ref(v_arg_4873_);
lean_dec_ref(v_arg_4870_);
goto v___jp_4863_;
}
else
{
lean_object* v___x_4879_; 
v___x_4879_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4873_, v_arg_4870_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_);
lean_dec_ref(v_arg_4870_);
return v___x_4879_;
}
}
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_a_4880_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4866_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4866_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
v___jp_4863_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
return v___x_4865_;
}
}
}
LEAN_EXPORT void l_Int_reduceNatCast___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4857_ = stack[0].m_obj;
lean_object* v_a_4858_ = stack[1].m_obj;
lean_object* v_a_4859_ = stack[2].m_obj;
lean_object* v_a_4860_ = stack[3].m_obj;
lean_object* v_a_4861_ = stack[4].m_obj;
lean_object* v_res_4888_;
v_res_4888_ = l_Int_reduceNatCast___redArg(v_e_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_);
stack->m_obj
 = v_res_4888_;
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object* v_e_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_Int_reduceNatCast___redArg(v_e_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
return v_res_4895_;
}
}
lean_object* l_Int_reduceNatCast(lean_object* v_e_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = l_Int_reduceNatCast___redArg(v_e_4896_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
return v___x_4905_;
}
}
LEAN_EXPORT void l_Int_reduceNatCast_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4896_ = stack[0].m_obj;
lean_object* v_a_4897_ = stack[1].m_obj;
lean_object* v_a_4898_ = stack[2].m_obj;
lean_object* v_a_4899_ = stack[3].m_obj;
lean_object* v_a_4900_ = stack[4].m_obj;
lean_object* v_a_4901_ = stack[5].m_obj;
lean_object* v_a_4902_ = stack[6].m_obj;
lean_object* v_a_4903_ = stack[7].m_obj;
lean_object* v_res_4906_;
v_res_4906_ = l_Int_reduceNatCast(v_e_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
stack->m_obj
 = v_res_4906_;
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object* v_e_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Int_reduceNatCast(v_e_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_a_4909_);
lean_dec(v_a_4908_);
return v_res_4916_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4936_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4937_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4934_, v___x_4935_, v___x_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4938_;
v_res_4938_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_();
stack->m_obj
 = v_res_4938_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23____boxed(lean_object* v_a_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_();
return v_res_4940_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4941_);
return v___x_4942_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4944_; uint8_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4945_ = 1;
v___x_4946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_);
v___x_4947_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4944_, v___x_4945_, v___x_4946_);
return v___x_4947_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4948_;
v_res_4948_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_();
stack->m_obj
 = v_res_4948_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25____boxed(lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_();
return v_res_4950_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4952_; uint8_t v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4953_ = 1;
v___x_4954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_);
v___x_4955_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4952_, v___x_4953_, v___x_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4956_;
v_res_4956_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_();
stack->m_obj
 = v_res_4956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27____boxed(lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_();
return v_res_4958_;
}
}
lean_object* l_Int_reduceNatCast_x27___redArg(lean_object* v_e_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4963_, v_a_4965_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4974_; uint8_t v___x_4975_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc(v_a_4973_);
lean_dec_ref_known(v___x_4972_, 1);
v___x_4974_ = l_Lean_Expr_cleanupAnnotations(v_a_4973_);
v___x_4975_ = l_Lean_Expr_isApp(v___x_4974_);
if (v___x_4975_ == 0)
{
lean_dec_ref(v___x_4974_);
goto v___jp_4969_;
}
else
{
lean_object* v_arg_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; 
v_arg_4976_ = lean_ctor_get(v___x_4974_, 1);
lean_inc_ref(v_arg_4976_);
v___x_4977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4974_);
v___x_4978_ = l_Lean_Expr_isApp(v___x_4977_);
if (v___x_4978_ == 0)
{
lean_dec_ref(v___x_4977_);
lean_dec_ref(v_arg_4976_);
goto v___jp_4969_;
}
else
{
lean_object* v_arg_4979_; lean_object* v___x_4980_; uint8_t v___x_4981_; 
v_arg_4979_ = lean_ctor_get(v___x_4977_, 1);
lean_inc_ref(v_arg_4979_);
v___x_4980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4977_);
v___x_4981_ = l_Lean_Expr_isApp(v___x_4980_);
if (v___x_4981_ == 0)
{
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_arg_4979_);
lean_dec_ref(v_arg_4976_);
goto v___jp_4969_;
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; uint8_t v___x_4984_; 
v___x_4982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4980_);
v___x_4983_ = ((lean_object*)(l_Int_reduceNatCast_x27___redArg___closed__1));
v___x_4984_ = l_Lean_Expr_isConstOf(v___x_4982_, v___x_4983_);
lean_dec_ref(v___x_4982_);
if (v___x_4984_ == 0)
{
lean_dec_ref(v_arg_4979_);
lean_dec_ref(v_arg_4976_);
goto v___jp_4969_;
}
else
{
lean_object* v___x_4985_; 
v___x_4985_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4979_, v_arg_4976_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec_ref(v_arg_4976_);
return v___x_4985_;
}
}
}
}
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
v_a_4986_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4972_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4972_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
v___jp_4969_:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4971_, 0, v___x_4970_);
return v___x_4971_;
}
}
}
LEAN_EXPORT void l_Int_reduceNatCast_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4963_ = stack[0].m_obj;
lean_object* v_a_4964_ = stack[1].m_obj;
lean_object* v_a_4965_ = stack[2].m_obj;
lean_object* v_a_4966_ = stack[3].m_obj;
lean_object* v_a_4967_ = stack[4].m_obj;
lean_object* v_res_4994_;
v_res_4994_ = l_Int_reduceNatCast_x27___redArg(v_e_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
stack->m_obj
 = v_res_4994_;
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object* v_e_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Int_reduceNatCast_x27___redArg(v_e_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
return v_res_5001_;
}
}
lean_object* l_Int_reduceNatCast_x27(lean_object* v_e_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v___x_5011_; 
v___x_5011_ = l_Int_reduceNatCast_x27___redArg(v_e_5002_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
return v___x_5011_;
}
}
LEAN_EXPORT void l_Int_reduceNatCast_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5002_ = stack[0].m_obj;
lean_object* v_a_5003_ = stack[1].m_obj;
lean_object* v_a_5004_ = stack[2].m_obj;
lean_object* v_a_5005_ = stack[3].m_obj;
lean_object* v_a_5006_ = stack[4].m_obj;
lean_object* v_a_5007_ = stack[5].m_obj;
lean_object* v_a_5008_ = stack[6].m_obj;
lean_object* v_a_5009_ = stack[7].m_obj;
lean_object* v_res_5012_;
v_res_5012_ = l_Int_reduceNatCast_x27(v_e_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
stack->m_obj
 = v_res_5012_;
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object* v_e_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Int_reduceNatCast_x27(v_e_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
lean_dec(v_a_5016_);
lean_dec_ref(v_a_5015_);
lean_dec(v_a_5014_);
return v_res_5022_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_5029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_5030_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_5031_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5028_, v___x_5029_, v___x_5030_);
return v___x_5031_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5032_;
v_res_5032_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_();
stack->m_obj
 = v_res_5032_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23____boxed(lean_object* v_a_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_();
return v_res_5034_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_5038_; uint8_t v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_5039_ = 1;
v___x_5040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_);
v___x_5041_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5038_, v___x_5039_, v___x_5040_);
return v___x_5041_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5042_;
v_res_5042_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_();
stack->m_obj
 = v_res_5042_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25____boxed(lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_();
return v_res_5044_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_5046_; uint8_t v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_5047_ = 1;
v___x_5048_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_);
v___x_5049_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5046_, v___x_5047_, v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5050_;
v_res_5050_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_();
stack->m_obj
 = v_res_5050_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27____boxed(lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_();
return v_res_5052_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
}
#ifdef __cplusplus
}
#endif
