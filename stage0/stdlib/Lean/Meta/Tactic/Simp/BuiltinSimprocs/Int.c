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
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getIntValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___redArg___boxed(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Int_fromExpr_x3f___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f(lean_object* v_e_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_getIntValue_x3f(v_e_15_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Int_fromExpr_x3f___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Int_fromExpr_x3f(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = l_Lean_Level_ofNat(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__5);
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__6);
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4));
v___x_51_ = l_Lean_Expr_const___override(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9));
v___x_57_ = l_Lean_Expr_const___override(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__12));
v___x_64_ = l_Lean_Expr_const___override(v___x_63_, v___x_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg(lean_object* v_declName_65_, lean_object* v_arity_66_, lean_object* v_op_67_, lean_object* v_e_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_Lean_Expr_isAppOfArity(v_e_68_, v_declName_65_, v_arity_66_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec_ref(v_op_67_);
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l_Lean_Expr_appArg_x21(v_e_68_);
v___x_78_ = l_Lean_Meta_getIntValue_x3f(v___x_77_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_104_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_104_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_104_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_104_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___y_84_; 
if (lean_obj_tag(v_a_79_) == 1)
{
lean_object* v_val_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_val_89_ = lean_ctor_get(v_a_79_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_a_79_, 1);
v___x_90_ = lean_apply_1(v_op_67_, v_val_89_);
v___x_91_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_92_ = lean_int_dec_le(v___x_91_, v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_94_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_95_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_96_ = lean_int_neg(v___x_90_);
lean_dec(v___x_90_);
v___x_97_ = l_Int_toNat(v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = l_Lean_instToExprInt_mkNat(v___x_97_);
v___x_99_ = l_Lean_mkApp3(v___x_93_, v___x_94_, v___x_95_, v___x_98_);
v___y_84_ = v___x_99_;
goto v___jp_83_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_Int_toNat(v___x_90_);
lean_dec(v___x_90_);
v___x_101_ = l_Lean_instToExprInt_mkNat(v___x_100_);
v___y_84_ = v___x_101_;
goto v___jp_83_;
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_del_object(v___x_81_);
lean_dec(v_a_79_);
lean_dec_ref(v_op_67_);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___y_84_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_85_);
v___x_87_ = v___x_81_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v_op_67_);
v_a_105_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_78_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_78_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___boxed(lean_object* v_declName_113_, lean_object* v_arity_114_, lean_object* v_op_115_, lean_object* v_e_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg(v_declName_113_, v_arity_114_, v_op_115_, v_e_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_e_116_);
lean_dec(v_declName_113_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary(lean_object* v_declName_123_, lean_object* v_arity_124_, lean_object* v_op_125_, lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_isAppOfArity(v_e_126_, v_declName_123_, v_arity_124_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref(v_op_125_);
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = l_Lean_Expr_appArg_x21(v_e_126_);
v___x_139_ = l_Lean_Meta_getIntValue_x3f(v___x_138_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_165_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_165_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_165_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_165_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___y_145_; 
if (lean_obj_tag(v_a_140_) == 1)
{
lean_object* v_val_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_val_150_ = lean_ctor_get(v_a_140_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v_a_140_, 1);
v___x_151_ = lean_apply_1(v_op_125_, v_val_150_);
v___x_152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_153_ = lean_int_dec_le(v___x_152_, v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_157_ = lean_int_neg(v___x_151_);
lean_dec(v___x_151_);
v___x_158_ = l_Int_toNat(v___x_157_);
lean_dec(v___x_157_);
v___x_159_ = l_Lean_instToExprInt_mkNat(v___x_158_);
v___x_160_ = l_Lean_mkApp3(v___x_154_, v___x_155_, v___x_156_, v___x_159_);
v___y_145_ = v___x_160_;
goto v___jp_144_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Int_toNat(v___x_151_);
lean_dec(v___x_151_);
v___x_162_ = l_Lean_instToExprInt_mkNat(v___x_161_);
v___y_145_ = v___x_162_;
goto v___jp_144_;
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_del_object(v___x_142_);
lean_dec(v_a_140_);
lean_dec_ref(v_op_125_);
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___y_145_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_146_);
v___x_148_ = v___x_142_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec_ref(v_op_125_);
v_a_166_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_139_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_139_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___boxed(lean_object* v_declName_174_, lean_object* v_arity_175_, lean_object* v_op_176_, lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary(v_declName_174_, v_arity_175_, v_op_176_, v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_e_177_);
lean_dec(v_declName_174_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg(lean_object* v_declName_187_, lean_object* v_arity_188_, lean_object* v_op_189_, lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Lean_Expr_isAppOfArity(v_e_190_, v_declName_187_, v_arity_188_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v_op_189_);
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = l_Lean_Expr_appFn_x21(v_e_190_);
v___x_200_ = l_Lean_Expr_appArg_x21(v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_Lean_Meta_getIntValue_x3f(v___x_200_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_255_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_255_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_255_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_255_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
if (lean_obj_tag(v_a_202_) == 1)
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_250_; 
v_val_206_ = lean_ctor_get(v_a_202_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_a_202_);
if (v_isSharedCheck_250_ == 0)
{
v___x_208_ = v_a_202_;
v_isShared_209_ = v_isSharedCheck_250_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v_a_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_250_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_Lean_Expr_appArg_x21(v_e_190_);
v___x_211_ = l_Lean_Meta_getIntValue_x3f(v___x_210_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_241_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_241_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_241_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_241_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___y_217_; 
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
lean_del_object(v___x_204_);
v_val_224_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v_a_212_, 1);
v___x_225_ = lean_apply_2(v_op_189_, v_val_206_, v_val_224_);
v___x_226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_227_ = lean_int_dec_le(v___x_226_, v___x_225_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_231_ = lean_int_neg(v___x_225_);
lean_dec(v___x_225_);
v___x_232_ = l_Int_toNat(v___x_231_);
lean_dec(v___x_231_);
v___x_233_ = l_Lean_instToExprInt_mkNat(v___x_232_);
v___x_234_ = l_Lean_mkApp3(v___x_228_, v___x_229_, v___x_230_, v___x_233_);
v___y_217_ = v___x_234_;
goto v___jp_216_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = l_Int_toNat(v___x_225_);
lean_dec(v___x_225_);
v___x_236_ = l_Lean_instToExprInt_mkNat(v___x_235_);
v___y_217_ = v___x_236_;
goto v___jp_216_;
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_del_object(v___x_214_);
lean_dec(v_a_212_);
lean_del_object(v___x_208_);
lean_dec(v_val_206_);
lean_dec_ref(v_op_189_);
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_237_);
v___x_239_ = v___x_204_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
v___jp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 0);
lean_ctor_set(v___x_208_, 0, v___y_217_);
v___x_219_ = v___x_208_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___y_217_);
v___x_219_ = v_reuseFailAlloc_223_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_219_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_del_object(v___x_208_);
lean_dec(v_val_206_);
lean_del_object(v___x_204_);
lean_dec_ref(v_op_189_);
v_a_242_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_211_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_211_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v_a_202_);
lean_dec_ref(v_op_189_);
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_251_);
v___x_253_ = v___x_204_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_op_189_);
v_a_256_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_201_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_201_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg___boxed(lean_object* v_declName_264_, lean_object* v_arity_265_, lean_object* v_op_266_, lean_object* v_e_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___redArg(v_declName_264_, v_arity_265_, v_op_266_, v_e_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec_ref(v_e_267_);
lean_dec(v_declName_264_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin(lean_object* v_declName_274_, lean_object* v_arity_275_, lean_object* v_op_276_, lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Lean_Expr_isAppOfArity(v_e_277_, v_declName_274_, v_arity_275_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec_ref(v_op_276_);
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = l_Lean_Expr_appFn_x21(v_e_277_);
v___x_290_ = l_Lean_Expr_appArg_x21(v___x_289_);
lean_dec_ref(v___x_289_);
v___x_291_ = l_Lean_Meta_getIntValue_x3f(v___x_290_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_345_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_345_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_345_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_345_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
if (lean_obj_tag(v_a_292_) == 1)
{
lean_object* v_val_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_340_; 
v_val_296_ = lean_ctor_get(v_a_292_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_340_ == 0)
{
v___x_298_ = v_a_292_;
v_isShared_299_ = v_isSharedCheck_340_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_val_296_);
lean_dec(v_a_292_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_340_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_Expr_appArg_x21(v_e_277_);
v___x_301_ = l_Lean_Meta_getIntValue_x3f(v___x_300_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_331_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_331_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_331_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_331_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___y_307_; 
if (lean_obj_tag(v_a_302_) == 1)
{
lean_object* v_val_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
lean_del_object(v___x_294_);
v_val_314_ = lean_ctor_get(v_a_302_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v_a_302_, 1);
v___x_315_ = lean_apply_2(v_op_276_, v_val_296_, v_val_314_);
v___x_316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_317_ = lean_int_dec_le(v___x_316_, v___x_315_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_320_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_321_ = lean_int_neg(v___x_315_);
lean_dec(v___x_315_);
v___x_322_ = l_Int_toNat(v___x_321_);
lean_dec(v___x_321_);
v___x_323_ = l_Lean_instToExprInt_mkNat(v___x_322_);
v___x_324_ = l_Lean_mkApp3(v___x_318_, v___x_319_, v___x_320_, v___x_323_);
v___y_307_ = v___x_324_;
goto v___jp_306_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = l_Int_toNat(v___x_315_);
lean_dec(v___x_315_);
v___x_326_ = l_Lean_instToExprInt_mkNat(v___x_325_);
v___y_307_ = v___x_326_;
goto v___jp_306_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_del_object(v___x_304_);
lean_dec(v_a_302_);
lean_del_object(v___x_298_);
lean_dec(v_val_296_);
lean_dec_ref(v_op_276_);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_327_);
v___x_329_ = v___x_294_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
v___jp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 0);
lean_ctor_set(v___x_298_, 0, v___y_307_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___y_307_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_309_);
v___x_311_ = v___x_304_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_del_object(v___x_298_);
lean_dec(v_val_296_);
lean_del_object(v___x_294_);
lean_dec_ref(v_op_276_);
v_a_332_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_301_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_301_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_a_292_);
lean_dec_ref(v_op_276_);
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_341_);
v___x_343_ = v___x_294_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v_op_276_);
v_a_346_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_291_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_291_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin___boxed(lean_object* v_declName_354_, lean_object* v_arity_355_, lean_object* v_op_356_, lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBin(v_declName_354_, v_arity_355_, v_op_356_, v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_e_357_);
lean_dec(v_declName_354_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(lean_object* v_name_367_, lean_object* v_op_368_, lean_object* v_e_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(2u);
v___x_376_ = l_Lean_Expr_isAppOfArity(v_e_369_, v_name_367_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_op_368_);
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = l_Lean_Expr_appFn_x21(v_e_369_);
v___x_380_ = l_Lean_Expr_appArg_x21(v___x_379_);
lean_dec_ref(v___x_379_);
v___x_381_ = l_Lean_Meta_getIntValue_x3f(v___x_380_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_435_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_435_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_435_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_435_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
if (lean_obj_tag(v_a_382_) == 1)
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_430_; 
v_val_386_ = lean_ctor_get(v_a_382_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_a_382_);
if (v_isSharedCheck_430_ == 0)
{
v___x_388_ = v_a_382_;
v_isShared_389_ = v_isSharedCheck_430_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v_a_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_430_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = l_Lean_Expr_appArg_x21(v_e_369_);
v___x_391_ = l_Lean_Meta_getNatValue_x3f(v___x_390_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec_ref(v___x_390_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_421_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_421_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_421_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_421_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___y_397_; 
if (lean_obj_tag(v_a_392_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
lean_del_object(v___x_384_);
v_val_404_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v_a_392_, 1);
v___x_405_ = lean_apply_2(v_op_368_, v_val_386_, v_val_404_);
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_407_ = lean_int_dec_le(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_411_ = lean_int_neg(v___x_405_);
lean_dec(v___x_405_);
v___x_412_ = l_Int_toNat(v___x_411_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_instToExprInt_mkNat(v___x_412_);
v___x_414_ = l_Lean_mkApp3(v___x_408_, v___x_409_, v___x_410_, v___x_413_);
v___y_397_ = v___x_414_;
goto v___jp_396_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = l_Int_toNat(v___x_405_);
lean_dec(v___x_405_);
v___x_416_ = l_Lean_instToExprInt_mkNat(v___x_415_);
v___y_397_ = v___x_416_;
goto v___jp_396_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_del_object(v___x_394_);
lean_dec(v_a_392_);
lean_del_object(v___x_388_);
lean_dec(v_val_386_);
lean_dec_ref(v_op_368_);
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_417_);
v___x_419_ = v___x_384_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
v___jp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v___y_397_);
v___x_399_ = v___x_388_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___y_397_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_399_);
v___x_401_ = v___x_394_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_del_object(v___x_388_);
lean_dec(v_val_386_);
lean_del_object(v___x_384_);
lean_dec_ref(v_op_368_);
v_a_422_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_391_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_391_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_dec(v_a_382_);
lean_dec_ref(v_op_368_);
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_431_);
v___x_433_ = v___x_384_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
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
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_op_368_);
v_a_436_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_381_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_381_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg___boxed(lean_object* v_name_444_, lean_object* v_op_445_, lean_object* v_e_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v_name_444_, v_op_445_, v_e_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec_ref(v_e_446_);
lean_dec(v_name_444_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp(lean_object* v_name_453_, lean_object* v_op_454_, lean_object* v_e_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v_name_453_, v_op_454_, v_e_455_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___boxed(lean_object* v_name_465_, lean_object* v_op_466_, lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp(v_name_465_, v_op_466_, v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_e_467_);
lean_dec(v_name_465_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg(lean_object* v_declName_479_, lean_object* v_arity_480_, lean_object* v_op_481_, lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_Expr_isAppOfArity(v_e_482_, v_declName_479_, v_arity_480_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_Expr_appFn_x21(v_e_482_);
v___x_492_ = l_Lean_Expr_appArg_x21(v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = l_Lean_Meta_getIntValue_x3f(v___x_492_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_526_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_526_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_526_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_526_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
if (lean_obj_tag(v_a_494_) == 1)
{
lean_object* v_val_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
lean_del_object(v___x_496_);
v_val_498_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v_a_494_, 1);
v___x_499_ = l_Lean_Expr_appArg_x21(v_e_482_);
v___x_500_ = l_Lean_Meta_getIntValue_x3f(v___x_499_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_513_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_513_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_513_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_513_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_val_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
lean_del_object(v___x_503_);
v_val_505_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_a_501_, 1);
v___x_506_ = lean_apply_2(v_op_481_, v_val_498_, v_val_505_);
v___x_507_ = lean_unbox(v___x_506_);
v___x_508_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_482_, v___x_507_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec(v_a_501_);
lean_dec(v_val_498_);
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v___x_509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_509_);
v___x_511_ = v___x_503_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_val_498_);
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v_a_514_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_500_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_500_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
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
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v_a_494_);
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_522_);
v___x_524_ = v___x_496_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_e_482_);
lean_dec_ref(v_op_481_);
v_a_527_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_493_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_493_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___boxed(lean_object* v_declName_535_, lean_object* v_arity_536_, lean_object* v_op_537_, lean_object* v_e_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg(v_declName_535_, v_arity_536_, v_op_537_, v_e_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_declName_535_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred(lean_object* v_declName_545_, lean_object* v_arity_546_, lean_object* v_op_547_, lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = l_Lean_Expr_isAppOfArity(v_e_548_, v_declName_545_, v_arity_546_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = l_Lean_Expr_appFn_x21(v_e_548_);
v___x_561_ = l_Lean_Expr_appArg_x21(v___x_560_);
lean_dec_ref(v___x_560_);
v___x_562_ = l_Lean_Meta_getIntValue_x3f(v___x_561_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_595_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_595_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_595_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_595_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_a_563_) == 1)
{
lean_object* v_val_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_del_object(v___x_565_);
v_val_567_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_a_563_, 1);
v___x_568_ = l_Lean_Expr_appArg_x21(v_e_548_);
v___x_569_ = l_Lean_Meta_getIntValue_x3f(v___x_568_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_582_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_582_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_582_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_582_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; 
lean_del_object(v___x_572_);
v_val_574_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_a_570_, 1);
v___x_575_ = lean_apply_2(v_op_547_, v_val_567_, v_val_574_);
v___x_576_ = lean_unbox(v___x_575_);
v___x_577_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_548_, v___x_576_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec(v_a_570_);
lean_dec(v_val_567_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_578_);
v___x_580_ = v___x_572_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_val_567_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v_a_583_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_569_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_569_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec(v_a_563_);
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_591_);
v___x_593_ = v___x_565_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_e_548_);
lean_dec_ref(v_op_547_);
v_a_596_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_562_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_562_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___boxed(lean_object* v_declName_604_, lean_object* v_arity_605_, lean_object* v_op_606_, lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred(v_declName_604_, v_arity_605_, v_op_606_, v_e_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_declName_604_);
return v_res_616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_box(0);
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__2));
v___x_624_ = l_Lean_mkConst(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_box(0);
v___x_630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__5));
v___x_631_ = l_Lean_mkConst(v___x_630_, v___x_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg(lean_object* v_declName_632_, lean_object* v_arity_633_, lean_object* v_op_634_, lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Expr_isAppOfArity(v_e_635_, v_declName_632_, v_arity_633_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_op_634_);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = l_Lean_Expr_appFn_x21(v_e_635_);
v___x_645_ = l_Lean_Expr_appArg_x21(v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = l_Lean_Meta_getIntValue_x3f(v___x_645_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_692_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_692_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_692_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_692_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
if (lean_obj_tag(v_a_647_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_687_; 
v_val_651_ = lean_ctor_get(v_a_647_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_687_ == 0)
{
v___x_653_ = v_a_647_;
v_isShared_654_ = v_isSharedCheck_687_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v_a_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_687_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = l_Lean_Expr_appArg_x21(v_e_635_);
v___x_656_ = l_Lean_Meta_getIntValue_x3f(v___x_655_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_678_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_678_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_678_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_678_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___y_662_; 
if (lean_obj_tag(v_a_657_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
lean_del_object(v___x_649_);
v_val_669_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v_a_657_, 1);
v___x_670_ = lean_apply_2(v_op_634_, v_val_651_, v_val_669_);
v___x_671_ = lean_unbox(v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_662_ = v___x_672_;
goto v___jp_661_;
}
else
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_662_ = v___x_673_;
goto v___jp_661_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_del_object(v___x_659_);
lean_dec(v_a_657_);
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_dec_ref(v_op_634_);
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_674_);
v___x_676_ = v___x_649_;
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
v___jp_661_:
{
lean_object* v___x_664_; 
lean_inc_ref(v___y_662_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 0, v___y_662_);
v___x_664_ = v___x_653_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___y_662_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_664_);
v___x_666_ = v___x_659_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_del_object(v___x_649_);
lean_dec_ref(v_op_634_);
v_a_679_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_656_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_656_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec(v_a_647_);
lean_dec_ref(v_op_634_);
v___x_688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_688_);
v___x_690_ = v___x_649_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_op_634_);
v_a_693_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_646_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_646_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___boxed(lean_object* v_declName_701_, lean_object* v_arity_702_, lean_object* v_op_703_, lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg(v_declName_701_, v_arity_702_, v_op_703_, v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_e_704_);
lean_dec(v_declName_701_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred(lean_object* v_declName_711_, lean_object* v_arity_712_, lean_object* v_op_713_, lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_isAppOfArity(v_e_714_, v_declName_711_, v_arity_712_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v_op_713_);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = l_Lean_Expr_appFn_x21(v_e_714_);
v___x_727_ = l_Lean_Expr_appArg_x21(v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = l_Lean_Meta_getIntValue_x3f(v___x_727_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_774_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_774_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_774_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_774_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
if (lean_obj_tag(v_a_729_) == 1)
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_769_; 
v_val_733_ = lean_ctor_get(v_a_729_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_769_ == 0)
{
v___x_735_ = v_a_729_;
v_isShared_736_ = v_isSharedCheck_769_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v_a_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_769_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Lean_Expr_appArg_x21(v_e_714_);
v___x_738_ = l_Lean_Meta_getIntValue_x3f(v___x_737_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_760_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_760_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_760_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_760_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___y_744_; 
if (lean_obj_tag(v_a_739_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
lean_del_object(v___x_731_);
v_val_751_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_a_739_, 1);
v___x_752_ = lean_apply_2(v_op_713_, v_val_733_, v_val_751_);
v___x_753_ = lean_unbox(v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_744_ = v___x_754_;
goto v___jp_743_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_744_ = v___x_755_;
goto v___jp_743_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_del_object(v___x_741_);
lean_dec(v_a_739_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_op_713_);
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_756_);
v___x_758_ = v___x_731_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
v___jp_743_:
{
lean_object* v___x_746_; 
lean_inc_ref(v___y_744_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 0);
lean_ctor_set(v___x_735_, 0, v___y_744_);
v___x_746_ = v___x_735_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___y_744_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_746_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_del_object(v___x_731_);
lean_dec_ref(v_op_713_);
v_a_761_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_738_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_738_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v_a_729_);
lean_dec_ref(v_op_713_);
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_770_);
v___x_772_ = v___x_731_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v_op_713_);
v_a_775_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_728_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_728_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___boxed(lean_object* v_declName_783_, lean_object* v_arity_784_, lean_object* v_op_785_, lean_object* v_e_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred(v_declName_783_, v_arity_784_, v_op_785_, v_e_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_e_786_);
lean_dec(v_declName_783_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg(lean_object* v_e_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___y_814_; lean_object* v___x_817_; 
lean_inc_ref(v_e_801_);
v___x_817_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_801_, v_a_803_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = l_Lean_Expr_cleanupAnnotations(v_a_818_);
v___x_820_ = l_Lean_Expr_isApp(v___x_819_);
if (v___x_820_ == 0)
{
lean_dec_ref(v___x_819_);
lean_dec_ref(v_e_801_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_821_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_arg_821_ = lean_ctor_get(v___x_819_, 1);
lean_inc_ref(v_arg_821_);
v___x_858_ = l_Lean_Expr_appFnCleanup___redArg(v___x_819_);
v___x_859_ = l_Lean_Expr_isApp(v___x_858_);
if (v___x_859_ == 0)
{
lean_dec_ref(v___x_858_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_e_801_);
goto v___jp_810_;
}
else
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = l_Lean_Expr_appFnCleanup___redArg(v___x_858_);
v___x_861_ = l_Lean_Expr_isApp(v___x_860_);
if (v___x_861_ == 0)
{
lean_dec_ref(v___x_860_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_e_801_);
goto v___jp_810_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_860_);
v___x_863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4));
v___x_864_ = l_Lean_Expr_isConstOf(v___x_862_, v___x_863_);
lean_dec_ref(v___x_862_);
if (v___x_864_ == 0)
{
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_e_801_);
goto v___jp_810_;
}
else
{
lean_object* v___x_865_; 
lean_inc_ref(v_arg_821_);
v___x_865_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_821_, v_a_803_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_894_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_894_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = l_Lean_Expr_cleanupAnnotations(v_a_866_);
v___x_871_ = l_Lean_Expr_isApp(v___x_870_);
if (v___x_871_ == 0)
{
lean_dec_ref(v___x_870_);
lean_del_object(v___x_868_);
lean_dec_ref(v_e_801_);
v___y_823_ = v_a_802_;
v___y_824_ = v_a_803_;
v___y_825_ = v_a_804_;
v___y_826_ = v_a_805_;
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
lean_del_object(v___x_868_);
lean_dec_ref(v_e_801_);
v___y_823_ = v_a_802_;
v___y_824_ = v_a_803_;
v___y_825_ = v_a_804_;
v___y_826_ = v_a_805_;
goto v___jp_822_;
}
else
{
lean_object* v_arg_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_arg_874_ = lean_ctor_get(v___x_872_, 1);
lean_inc_ref(v_arg_874_);
v___x_875_ = l_Lean_Expr_appFnCleanup___redArg(v___x_872_);
v___x_876_ = l_Lean_Expr_isApp(v___x_875_);
if (v___x_876_ == 0)
{
lean_dec_ref(v___x_875_);
lean_dec_ref(v_arg_874_);
lean_del_object(v___x_868_);
lean_dec_ref(v_e_801_);
v___y_823_ = v_a_802_;
v___y_824_ = v_a_803_;
v___y_825_ = v_a_804_;
v___y_826_ = v_a_805_;
goto v___jp_822_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = l_Lean_Expr_appFnCleanup___redArg(v___x_875_);
v___x_878_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_879_ = l_Lean_Expr_isConstOf(v___x_877_, v___x_878_);
lean_dec_ref(v___x_877_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_arg_874_);
lean_del_object(v___x_868_);
lean_dec_ref(v_e_801_);
v___y_823_ = v_a_802_;
v___y_824_ = v_a_803_;
v___y_825_ = v_a_804_;
v___y_826_ = v_a_805_;
goto v___jp_822_;
}
else
{
if (lean_obj_tag(v_arg_874_) == 9)
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v_arg_874_, 0);
lean_inc_ref(v_a_880_);
lean_dec_ref_known(v_arg_874_, 1);
if (lean_obj_tag(v_a_880_) == 0)
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
v_val_881_ = lean_ctor_get(v_a_880_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_a_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_883_ = v_a_880_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v_a_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_nat_dec_eq(v_val_881_, v___x_885_);
lean_dec(v_val_881_);
if (v___x_886_ == 0)
{
lean_del_object(v___x_883_);
lean_del_object(v___x_868_);
lean_dec_ref(v_arg_821_);
goto v___jp_807_;
}
else
{
lean_object* v___x_888_; 
lean_dec_ref(v_e_801_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_arg_821_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_arg_821_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_888_);
v___x_890_ = v___x_868_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_880_);
lean_del_object(v___x_868_);
lean_dec_ref(v_arg_821_);
goto v___jp_807_;
}
}
else
{
lean_dec_ref(v_arg_874_);
lean_del_object(v___x_868_);
lean_dec_ref(v_arg_821_);
goto v___jp_807_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_e_801_);
v_a_895_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_865_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_865_);
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
}
}
v___jp_822_:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_getIntValue_x3f(v_arg_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_849_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_849_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
if (lean_obj_tag(v_a_828_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
lean_del_object(v___x_830_);
v_val_832_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v_a_828_, 1);
v___x_833_ = lean_int_neg(v_val_832_);
lean_dec(v_val_832_);
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_835_ = lean_int_dec_le(v___x_834_, v___x_833_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_836_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_837_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_839_ = lean_int_neg(v___x_833_);
lean_dec(v___x_833_);
v___x_840_ = l_Int_toNat(v___x_839_);
lean_dec(v___x_839_);
v___x_841_ = l_Lean_instToExprInt_mkNat(v___x_840_);
v___x_842_ = l_Lean_mkApp3(v___x_836_, v___x_837_, v___x_838_, v___x_841_);
v___y_814_ = v___x_842_;
goto v___jp_813_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = l_Int_toNat(v___x_833_);
lean_dec(v___x_833_);
v___x_844_ = l_Lean_instToExprInt_mkNat(v___x_843_);
v___y_814_ = v___x_844_;
goto v___jp_813_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec(v_a_828_);
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_845_);
v___x_847_ = v___x_830_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_827_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_827_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_e_801_);
v_a_903_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_817_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_817_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
v___jp_807_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_e_801_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
v___jp_810_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
v___jp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___y_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object* v_e_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Int_reduceNeg___redArg(v_e_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Int_reduceNeg___redArg(v_e_918_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object* v_e_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Int_reduceNeg(v_e_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_960_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_961_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_958_, v___x_959_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25____boxed(lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_();
return v_res_963_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_968_ = 1;
v___x_969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_);
v___x_970_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_967_, v___x_968_, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27____boxed(lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_();
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_25_));
v___x_975_ = 1;
v___x_976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_27_);
v___x_977_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_974_, v___x_975_, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29____boxed(lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_576612875____hygCtx___hyg_29_();
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object* v_e_980_, lean_object* v_a_981_){
_start:
{
lean_object* v___x_986_; 
lean_inc_ref(v_e_980_);
v___x_986_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_980_, v_a_981_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1004_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1004_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1004_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_Expr_cleanupAnnotations(v_a_987_);
v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_991_);
lean_del_object(v___x_989_);
lean_dec_ref(v_e_980_);
goto v___jp_983_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
v___x_994_ = l_Lean_Expr_isApp(v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_993_);
lean_del_object(v___x_989_);
lean_dec_ref(v_e_980_);
goto v___jp_983_;
}
else
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_993_);
v___x_996_ = l_Lean_Expr_isApp(v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v___x_995_);
lean_del_object(v___x_989_);
lean_dec_ref(v_e_980_);
goto v___jp_983_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_995_);
v___x_998_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_999_ = l_Lean_Expr_isConstOf(v___x_997_, v___x_998_);
lean_dec_ref(v___x_997_);
if (v___x_999_ == 0)
{
lean_del_object(v___x_989_);
lean_dec_ref(v_e_980_);
goto v___jp_983_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_e_980_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1000_);
v___x_1002_ = v___x_989_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_e_980_);
v_a_1005_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_986_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_986_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object* v_e_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Int_isPosValue___redArg(v_e_1013_, v_a_1014_);
lean_dec(v_a_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object* v_e_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Int_isPosValue___redArg(v_e_1017_, v_a_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object* v_e_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Int_isPosValue(v_e_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1056_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1057_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1054_, v___x_1055_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23____boxed(lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_();
return v_res_1059_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1064_ = 1;
v___x_1065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_);
v___x_1066_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1063_, v___x_1064_, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25____boxed(lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_();
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object* v_e_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = ((lean_object*)(l_Int_reduceAdd___redArg___closed__2));
v___x_1081_ = lean_unsigned_to_nat(6u);
v___x_1082_ = l_Lean_Expr_isAppOfArity(v_e_1074_, v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = l_Lean_Expr_appFn_x21(v_e_1074_);
v___x_1086_ = l_Lean_Expr_appArg_x21(v___x_1085_);
lean_dec_ref(v___x_1085_);
v___x_1087_ = l_Lean_Meta_getIntValue_x3f(v___x_1086_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1141_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1141_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1141_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
if (lean_obj_tag(v_a_1088_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1136_; 
v_val_1092_ = lean_ctor_get(v_a_1088_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1094_ = v_a_1088_;
v_isShared_1095_ = v_isSharedCheck_1136_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v_a_1088_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1136_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = l_Lean_Expr_appArg_x21(v_e_1074_);
v___x_1097_ = l_Lean_Meta_getIntValue_x3f(v___x_1096_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1127_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1127_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1127_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___y_1103_; 
if (lean_obj_tag(v_a_1098_) == 1)
{
lean_object* v_val_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
lean_del_object(v___x_1090_);
v_val_1110_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v_a_1098_, 1);
v___x_1111_ = lean_int_add(v_val_1092_, v_val_1110_);
lean_dec(v_val_1110_);
lean_dec(v_val_1092_);
v___x_1112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1113_ = lean_int_dec_le(v___x_1112_, v___x_1111_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1117_ = lean_int_neg(v___x_1111_);
lean_dec(v___x_1111_);
v___x_1118_ = l_Int_toNat(v___x_1117_);
lean_dec(v___x_1117_);
v___x_1119_ = l_Lean_instToExprInt_mkNat(v___x_1118_);
v___x_1120_ = l_Lean_mkApp3(v___x_1114_, v___x_1115_, v___x_1116_, v___x_1119_);
v___y_1103_ = v___x_1120_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l_Int_toNat(v___x_1111_);
lean_dec(v___x_1111_);
v___x_1122_ = l_Lean_instToExprInt_mkNat(v___x_1121_);
v___y_1103_ = v___x_1122_;
goto v___jp_1102_;
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_del_object(v___x_1100_);
lean_dec(v_a_1098_);
lean_del_object(v___x_1094_);
lean_dec(v_val_1092_);
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1123_);
v___x_1125_ = v___x_1090_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
v___jp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
lean_ctor_set(v___x_1094_, 0, v___y_1103_);
v___x_1105_ = v___x_1094_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___y_1103_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1105_);
v___x_1107_ = v___x_1100_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
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
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1094_);
lean_dec(v_val_1092_);
lean_del_object(v___x_1090_);
v_a_1128_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1097_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1097_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec(v_a_1088_);
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1137_);
v___x_1139_ = v___x_1090_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1087_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1087_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object* v_e_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Int_reduceAdd___redArg(v_e_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_e_1150_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object* v_e_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Int_reduceAdd___redArg(v_e_1157_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object* v_e_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Int_reduceAdd(v_e_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_e_1167_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1199_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1200_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1197_, v___x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26____boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_();
return v_res_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1207_ = 1;
v___x_1208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_);
v___x_1209_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1206_, v___x_1207_, v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28____boxed(lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_();
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1214_ = 1;
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_);
v___x_1216_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1213_, v___x_1214_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30____boxed(lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_();
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = ((lean_object*)(l_Int_reduceMul___redArg___closed__2));
v___x_1231_ = lean_unsigned_to_nat(6u);
v___x_1232_ = l_Lean_Expr_isAppOfArity(v_e_1224_, v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_Expr_appFn_x21(v_e_1224_);
v___x_1236_ = l_Lean_Expr_appArg_x21(v___x_1235_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = l_Lean_Meta_getIntValue_x3f(v___x_1236_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1291_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1291_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1291_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
if (lean_obj_tag(v_a_1238_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1286_; 
v_val_1242_ = lean_ctor_get(v_a_1238_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1238_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1244_ = v_a_1238_;
v_isShared_1245_ = v_isSharedCheck_1286_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_val_1242_);
lean_dec(v_a_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1286_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = l_Lean_Expr_appArg_x21(v_e_1224_);
v___x_1247_ = l_Lean_Meta_getIntValue_x3f(v___x_1246_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1277_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1277_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1277_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___y_1253_; 
if (lean_obj_tag(v_a_1248_) == 1)
{
lean_object* v_val_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
lean_del_object(v___x_1240_);
v_val_1260_ = lean_ctor_get(v_a_1248_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v_a_1248_, 1);
v___x_1261_ = lean_int_mul(v_val_1242_, v_val_1260_);
lean_dec(v_val_1260_);
lean_dec(v_val_1242_);
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1263_ = lean_int_dec_le(v___x_1262_, v___x_1261_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1267_ = lean_int_neg(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1268_ = l_Int_toNat(v___x_1267_);
lean_dec(v___x_1267_);
v___x_1269_ = l_Lean_instToExprInt_mkNat(v___x_1268_);
v___x_1270_ = l_Lean_mkApp3(v___x_1264_, v___x_1265_, v___x_1266_, v___x_1269_);
v___y_1253_ = v___x_1270_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Int_toNat(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1272_ = l_Lean_instToExprInt_mkNat(v___x_1271_);
v___y_1253_ = v___x_1272_;
goto v___jp_1252_;
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_del_object(v___x_1250_);
lean_dec(v_a_1248_);
lean_del_object(v___x_1244_);
lean_dec(v_val_1242_);
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1273_);
v___x_1275_ = v___x_1240_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
v___jp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1253_);
v___x_1255_ = v___x_1244_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___y_1253_);
v___x_1255_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1255_);
v___x_1257_ = v___x_1250_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_del_object(v___x_1244_);
lean_dec(v_val_1242_);
lean_del_object(v___x_1240_);
v_a_1278_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1247_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1247_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
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
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v_a_1238_);
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1287_);
v___x_1289_ = v___x_1240_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1237_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1237_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object* v_e_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Int_reduceMul___redArg(v_e_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec_ref(v_e_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object* v_e_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Int_reduceMul___redArg(v_e_1307_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Int_reduceMul(v_e_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_e_1317_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1349_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1350_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1347_, v___x_1348_, v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26____boxed(lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_();
return v_res_1352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1357_ = 1;
v___x_1358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_);
v___x_1359_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1356_, v___x_1357_, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28____boxed(lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_();
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1364_ = 1;
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_);
v___x_1366_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1363_, v___x_1364_, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30____boxed(lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_();
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object* v_e_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1380_ = ((lean_object*)(l_Int_reduceSub___redArg___closed__2));
v___x_1381_ = lean_unsigned_to_nat(6u);
v___x_1382_ = l_Lean_Expr_isAppOfArity(v_e_1374_, v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = l_Lean_Expr_appFn_x21(v_e_1374_);
v___x_1386_ = l_Lean_Expr_appArg_x21(v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l_Lean_Meta_getIntValue_x3f(v___x_1386_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1441_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1441_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1441_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
if (lean_obj_tag(v_a_1388_) == 1)
{
lean_object* v_val_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1436_; 
v_val_1392_ = lean_ctor_get(v_a_1388_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_a_1388_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1394_ = v_a_1388_;
v_isShared_1395_ = v_isSharedCheck_1436_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_val_1392_);
lean_dec(v_a_1388_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1436_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = l_Lean_Expr_appArg_x21(v_e_1374_);
v___x_1397_ = l_Lean_Meta_getIntValue_x3f(v___x_1396_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1427_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1427_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1427_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___y_1403_; 
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
lean_del_object(v___x_1390_);
v_val_1410_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1410_);
lean_dec_ref_known(v_a_1398_, 1);
v___x_1411_ = lean_int_sub(v_val_1392_, v_val_1410_);
lean_dec(v_val_1410_);
lean_dec(v_val_1392_);
v___x_1412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1413_ = lean_int_dec_le(v___x_1412_, v___x_1411_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1417_ = lean_int_neg(v___x_1411_);
lean_dec(v___x_1411_);
v___x_1418_ = l_Int_toNat(v___x_1417_);
lean_dec(v___x_1417_);
v___x_1419_ = l_Lean_instToExprInt_mkNat(v___x_1418_);
v___x_1420_ = l_Lean_mkApp3(v___x_1414_, v___x_1415_, v___x_1416_, v___x_1419_);
v___y_1403_ = v___x_1420_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = l_Int_toNat(v___x_1411_);
lean_dec(v___x_1411_);
v___x_1422_ = l_Lean_instToExprInt_mkNat(v___x_1421_);
v___y_1403_ = v___x_1422_;
goto v___jp_1402_;
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_del_object(v___x_1400_);
lean_dec(v_a_1398_);
lean_del_object(v___x_1394_);
lean_dec(v_val_1392_);
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1423_);
v___x_1425_ = v___x_1390_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
v___jp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1403_);
v___x_1405_ = v___x_1394_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___y_1403_);
v___x_1405_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1407_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1405_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_del_object(v___x_1394_);
lean_dec(v_val_1392_);
lean_del_object(v___x_1390_);
v_a_1428_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1397_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1397_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_dec(v_a_1388_);
v___x_1437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1437_);
v___x_1439_ = v___x_1390_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1387_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1387_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object* v_e_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Int_reduceSub___redArg(v_e_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec_ref(v_e_1450_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Int_reduceSub___redArg(v_e_1457_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object* v_e_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Int_reduceSub(v_e_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_e_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1499_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1500_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1497_, v___x_1498_, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26____boxed(lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_();
return v_res_1502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1507_ = 1;
v___x_1508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_);
v___x_1509_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1506_, v___x_1507_, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28____boxed(lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_();
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1514_ = 1;
v___x_1515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_);
v___x_1516_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1513_, v___x_1514_, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30____boxed(lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_();
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object* v_e_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = ((lean_object*)(l_Int_reduceDiv___redArg___closed__2));
v___x_1531_ = lean_unsigned_to_nat(6u);
v___x_1532_ = l_Lean_Expr_isAppOfArity(v_e_1524_, v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = l_Lean_Expr_appFn_x21(v_e_1524_);
v___x_1536_ = l_Lean_Expr_appArg_x21(v___x_1535_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = l_Lean_Meta_getIntValue_x3f(v___x_1536_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1591_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1591_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1591_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
if (lean_obj_tag(v_a_1538_) == 1)
{
lean_object* v_val_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1586_; 
v_val_1542_ = lean_ctor_get(v_a_1538_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1586_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_val_1542_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1586_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = l_Lean_Expr_appArg_x21(v_e_1524_);
v___x_1547_ = l_Lean_Meta_getIntValue_x3f(v___x_1546_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1577_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___y_1553_; 
if (lean_obj_tag(v_a_1548_) == 1)
{
lean_object* v_val_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
lean_del_object(v___x_1540_);
v_val_1560_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v_a_1548_, 1);
v___x_1561_ = lean_int_ediv(v_val_1542_, v_val_1560_);
lean_dec(v_val_1560_);
lean_dec(v_val_1542_);
v___x_1562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1563_ = lean_int_dec_le(v___x_1562_, v___x_1561_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1567_ = lean_int_neg(v___x_1561_);
lean_dec(v___x_1561_);
v___x_1568_ = l_Int_toNat(v___x_1567_);
lean_dec(v___x_1567_);
v___x_1569_ = l_Lean_instToExprInt_mkNat(v___x_1568_);
v___x_1570_ = l_Lean_mkApp3(v___x_1564_, v___x_1565_, v___x_1566_, v___x_1569_);
v___y_1553_ = v___x_1570_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = l_Int_toNat(v___x_1561_);
lean_dec(v___x_1561_);
v___x_1572_ = l_Lean_instToExprInt_mkNat(v___x_1571_);
v___y_1553_ = v___x_1572_;
goto v___jp_1552_;
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_del_object(v___x_1550_);
lean_dec(v_a_1548_);
lean_del_object(v___x_1544_);
lean_dec(v_val_1542_);
v___x_1573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1573_);
v___x_1575_ = v___x_1540_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
v___jp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 0);
lean_ctor_set(v___x_1544_, 0, v___y_1553_);
v___x_1555_ = v___x_1544_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___y_1553_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1555_);
v___x_1557_ = v___x_1550_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_del_object(v___x_1544_);
lean_dec(v_val_1542_);
lean_del_object(v___x_1540_);
v_a_1578_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1547_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1547_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec(v_a_1538_);
v___x_1587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1587_);
v___x_1589_ = v___x_1540_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_a_1592_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1537_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1537_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object* v_e_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Int_reduceDiv___redArg(v_e_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_e_1600_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object* v_e_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Int_reduceDiv___redArg(v_e_1607_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object* v_e_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Int_reduceDiv(v_e_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_e_1617_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1649_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1650_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1647_, v___x_1648_, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26____boxed(lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_();
return v_res_1652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1657_ = 1;
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_);
v___x_1659_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1656_, v___x_1657_, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28____boxed(lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1664_ = 1;
v___x_1665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_);
v___x_1666_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1663_, v___x_1664_, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30____boxed(lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_();
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object* v_e_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = ((lean_object*)(l_Int_reduceMod___redArg___closed__2));
v___x_1681_ = lean_unsigned_to_nat(6u);
v___x_1682_ = l_Lean_Expr_isAppOfArity(v_e_1674_, v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = l_Lean_Expr_appFn_x21(v_e_1674_);
v___x_1686_ = l_Lean_Expr_appArg_x21(v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_Lean_Meta_getIntValue_x3f(v___x_1686_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1741_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1741_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1741_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
if (lean_obj_tag(v_a_1688_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1736_; 
v_val_1692_ = lean_ctor_get(v_a_1688_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1688_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1694_ = v_a_1688_;
v_isShared_1695_ = v_isSharedCheck_1736_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_val_1692_);
lean_dec(v_a_1688_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1736_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = l_Lean_Expr_appArg_x21(v_e_1674_);
v___x_1697_ = l_Lean_Meta_getIntValue_x3f(v___x_1696_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1727_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1727_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1727_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___y_1703_; 
if (lean_obj_tag(v_a_1698_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
lean_del_object(v___x_1690_);
v_val_1710_ = lean_ctor_get(v_a_1698_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_a_1698_, 1);
v___x_1711_ = lean_int_emod(v_val_1692_, v_val_1710_);
lean_dec(v_val_1710_);
lean_dec(v_val_1692_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1713_ = lean_int_dec_le(v___x_1712_, v___x_1711_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1714_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1717_ = lean_int_neg(v___x_1711_);
lean_dec(v___x_1711_);
v___x_1718_ = l_Int_toNat(v___x_1717_);
lean_dec(v___x_1717_);
v___x_1719_ = l_Lean_instToExprInt_mkNat(v___x_1718_);
v___x_1720_ = l_Lean_mkApp3(v___x_1714_, v___x_1715_, v___x_1716_, v___x_1719_);
v___y_1703_ = v___x_1720_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = l_Int_toNat(v___x_1711_);
lean_dec(v___x_1711_);
v___x_1722_ = l_Lean_instToExprInt_mkNat(v___x_1721_);
v___y_1703_ = v___x_1722_;
goto v___jp_1702_;
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
lean_del_object(v___x_1700_);
lean_dec(v_a_1698_);
lean_del_object(v___x_1694_);
lean_dec(v_val_1692_);
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1723_);
v___x_1725_ = v___x_1690_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
v___jp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 0);
lean_ctor_set(v___x_1694_, 0, v___y_1703_);
v___x_1705_ = v___x_1694_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___y_1703_);
v___x_1705_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1705_);
v___x_1707_ = v___x_1700_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1694_);
lean_dec(v_val_1692_);
lean_del_object(v___x_1690_);
v_a_1728_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1697_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1697_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
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
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_dec(v_a_1688_);
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1737_);
v___x_1739_ = v___x_1690_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1742_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1687_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1687_);
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
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Int_reduceMod___redArg(v_e_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec_ref(v_e_1750_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Int_reduceMod___redArg(v_e_1757_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object* v_e_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Int_reduceMod(v_e_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_e_1767_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1799_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1800_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1797_, v___x_1798_, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26____boxed(lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_();
return v_res_1802_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1807_ = 1;
v___x_1808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_);
v___x_1809_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1806_, v___x_1807_, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28____boxed(lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_();
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1814_ = 1;
v___x_1815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_);
v___x_1816_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1813_, v___x_1814_, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30____boxed(lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_();
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object* v_e_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Int_reduceTDiv___redArg___closed__1));
v___x_1830_ = lean_unsigned_to_nat(2u);
v___x_1831_ = l_Lean_Expr_isAppOfArity(v_e_1823_, v___x_1829_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = l_Lean_Expr_appFn_x21(v_e_1823_);
v___x_1835_ = l_Lean_Expr_appArg_x21(v___x_1834_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = l_Lean_Meta_getIntValue_x3f(v___x_1835_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1890_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1890_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1890_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1885_; 
v_val_1841_ = lean_ctor_get(v_a_1837_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1843_ = v_a_1837_;
v_isShared_1844_ = v_isSharedCheck_1885_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_val_1841_);
lean_dec(v_a_1837_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1885_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = l_Lean_Expr_appArg_x21(v_e_1823_);
v___x_1846_ = l_Lean_Meta_getIntValue_x3f(v___x_1845_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1876_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1876_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1876_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___y_1852_; 
if (lean_obj_tag(v_a_1847_) == 1)
{
lean_object* v_val_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
lean_del_object(v___x_1839_);
v_val_1859_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_val_1859_);
lean_dec_ref_known(v_a_1847_, 1);
v___x_1860_ = lean_int_div(v_val_1841_, v_val_1859_);
lean_dec(v_val_1859_);
lean_dec(v_val_1841_);
v___x_1861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1862_ = lean_int_dec_le(v___x_1861_, v___x_1860_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1863_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1866_ = lean_int_neg(v___x_1860_);
lean_dec(v___x_1860_);
v___x_1867_ = l_Int_toNat(v___x_1866_);
lean_dec(v___x_1866_);
v___x_1868_ = l_Lean_instToExprInt_mkNat(v___x_1867_);
v___x_1869_ = l_Lean_mkApp3(v___x_1863_, v___x_1864_, v___x_1865_, v___x_1868_);
v___y_1852_ = v___x_1869_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = l_Int_toNat(v___x_1860_);
lean_dec(v___x_1860_);
v___x_1871_ = l_Lean_instToExprInt_mkNat(v___x_1870_);
v___y_1852_ = v___x_1871_;
goto v___jp_1851_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_del_object(v___x_1849_);
lean_dec(v_a_1847_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1872_);
v___x_1874_ = v___x_1839_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
v___jp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 0);
lean_ctor_set(v___x_1843_, 0, v___y_1852_);
v___x_1854_ = v___x_1843_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___y_1852_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1854_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1839_);
v_a_1877_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1846_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1846_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec(v_a_1837_);
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1886_);
v___x_1888_ = v___x_1839_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1836_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1836_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object* v_e_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Int_reduceTDiv___redArg(v_e_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec_ref(v_e_1899_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object* v_e_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Int_reduceTDiv___redArg(v_e_1906_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object* v_e_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Int_reduceTDiv(v_e_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_e_1916_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1943_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1944_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1941_, v___x_1942_, v___x_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21____boxed(lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_();
return v_res_1946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1951_ = 1;
v___x_1952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_);
v___x_1953_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1950_, v___x_1951_, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23____boxed(lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_();
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1958_ = 1;
v___x_1959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_);
v___x_1960_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1957_, v___x_1958_, v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25____boxed(lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_();
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = ((lean_object*)(l_Int_reduceTMod___redArg___closed__1));
v___x_1974_ = lean_unsigned_to_nat(2u);
v___x_1975_ = l_Lean_Expr_isAppOfArity(v_e_1967_, v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = l_Lean_Expr_appFn_x21(v_e_1967_);
v___x_1979_ = l_Lean_Expr_appArg_x21(v___x_1978_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = l_Lean_Meta_getIntValue_x3f(v___x_1979_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2034_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2034_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2034_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
if (lean_obj_tag(v_a_1981_) == 1)
{
lean_object* v_val_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2029_; 
v_val_1985_ = lean_ctor_get(v_a_1981_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1987_ = v_a_1981_;
v_isShared_1988_ = v_isSharedCheck_2029_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_val_1985_);
lean_dec(v_a_1981_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2029_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = l_Lean_Expr_appArg_x21(v_e_1967_);
v___x_1990_ = l_Lean_Meta_getIntValue_x3f(v___x_1989_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2020_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2020_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2020_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___y_1996_; 
if (lean_obj_tag(v_a_1991_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
lean_del_object(v___x_1983_);
v_val_2003_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v_a_1991_, 1);
v___x_2004_ = lean_int_mod(v_val_1985_, v_val_2003_);
lean_dec(v_val_2003_);
lean_dec(v_val_1985_);
v___x_2005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2006_ = lean_int_dec_le(v___x_2005_, v___x_2004_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2008_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2010_ = lean_int_neg(v___x_2004_);
lean_dec(v___x_2004_);
v___x_2011_ = l_Int_toNat(v___x_2010_);
lean_dec(v___x_2010_);
v___x_2012_ = l_Lean_instToExprInt_mkNat(v___x_2011_);
v___x_2013_ = l_Lean_mkApp3(v___x_2007_, v___x_2008_, v___x_2009_, v___x_2012_);
v___y_1996_ = v___x_2013_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = l_Int_toNat(v___x_2004_);
lean_dec(v___x_2004_);
v___x_2015_ = l_Lean_instToExprInt_mkNat(v___x_2014_);
v___y_1996_ = v___x_2015_;
goto v___jp_1995_;
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_del_object(v___x_1993_);
lean_dec(v_a_1991_);
lean_del_object(v___x_1987_);
lean_dec(v_val_1985_);
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2016_);
v___x_2018_ = v___x_1983_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
v___jp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 0);
lean_ctor_set(v___x_1987_, 0, v___y_1996_);
v___x_1998_ = v___x_1987_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___y_1996_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_2000_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1998_);
v___x_2000_ = v___x_1993_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_del_object(v___x_1987_);
lean_dec(v_val_1985_);
lean_del_object(v___x_1983_);
v_a_2021_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1990_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1990_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec(v_a_1981_);
v___x_2030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2030_);
v___x_2032_ = v___x_1983_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1980_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1980_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object* v_e_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Int_reduceTMod___redArg(v_e_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_e_2043_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object* v_e_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Int_reduceTMod___redArg(v_e_2050_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object* v_e_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Int_reduceTMod(v_e_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec_ref(v_e_2060_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2087_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2088_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2085_, v___x_2086_, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21____boxed(lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_();
return v_res_2090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2095_ = 1;
v___x_2096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_);
v___x_2097_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2094_, v___x_2095_, v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23____boxed(lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_();
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2102_ = 1;
v___x_2103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_);
v___x_2104_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2101_, v___x_2102_, v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25____boxed(lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_();
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2117_ = ((lean_object*)(l_Int_reduceFDiv___redArg___closed__1));
v___x_2118_ = lean_unsigned_to_nat(2u);
v___x_2119_ = l_Lean_Expr_isAppOfArity(v_e_2111_, v___x_2117_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = l_Lean_Expr_appFn_x21(v_e_2111_);
v___x_2123_ = l_Lean_Expr_appArg_x21(v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l_Lean_Meta_getIntValue_x3f(v___x_2123_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2178_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2178_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2178_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
if (lean_obj_tag(v_a_2125_) == 1)
{
lean_object* v_val_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2173_; 
v_val_2129_ = lean_ctor_get(v_a_2125_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2125_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2131_ = v_a_2125_;
v_isShared_2132_ = v_isSharedCheck_2173_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_val_2129_);
lean_dec(v_a_2125_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2173_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = l_Lean_Expr_appArg_x21(v_e_2111_);
v___x_2134_ = l_Lean_Meta_getIntValue_x3f(v___x_2133_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2164_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2164_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2164_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___y_2140_; 
if (lean_obj_tag(v_a_2135_) == 1)
{
lean_object* v_val_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
lean_del_object(v___x_2127_);
v_val_2147_ = lean_ctor_get(v_a_2135_, 0);
lean_inc(v_val_2147_);
lean_dec_ref_known(v_a_2135_, 1);
v___x_2148_ = l_Int_fdiv(v_val_2129_, v_val_2147_);
lean_dec(v_val_2147_);
lean_dec(v_val_2129_);
v___x_2149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2150_ = lean_int_dec_le(v___x_2149_, v___x_2148_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2151_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2154_ = lean_int_neg(v___x_2148_);
lean_dec(v___x_2148_);
v___x_2155_ = l_Int_toNat(v___x_2154_);
lean_dec(v___x_2154_);
v___x_2156_ = l_Lean_instToExprInt_mkNat(v___x_2155_);
v___x_2157_ = l_Lean_mkApp3(v___x_2151_, v___x_2152_, v___x_2153_, v___x_2156_);
v___y_2140_ = v___x_2157_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = l_Int_toNat(v___x_2148_);
lean_dec(v___x_2148_);
v___x_2159_ = l_Lean_instToExprInt_mkNat(v___x_2158_);
v___y_2140_ = v___x_2159_;
goto v___jp_2139_;
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_del_object(v___x_2137_);
lean_dec(v_a_2135_);
lean_del_object(v___x_2131_);
lean_dec(v_val_2129_);
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2160_);
v___x_2162_ = v___x_2127_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
v___jp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 0);
lean_ctor_set(v___x_2131_, 0, v___y_2140_);
v___x_2142_ = v___x_2131_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___y_2140_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2142_);
v___x_2144_ = v___x_2137_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_del_object(v___x_2131_);
lean_dec(v_val_2129_);
lean_del_object(v___x_2127_);
v_a_2165_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2134_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2134_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_dec(v_a_2125_);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2174_);
v___x_2176_ = v___x_2127_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
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
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_a_2179_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2124_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2124_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object* v_e_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Int_reduceFDiv___redArg(v_e_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec_ref(v_e_2187_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object* v_e_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Int_reduceFDiv___redArg(v_e_2194_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object* v_e_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Int_reduceFDiv(v_e_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_e_2204_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2231_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2232_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2229_, v___x_2230_, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21____boxed(lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_();
return v_res_2234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2239_ = 1;
v___x_2240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_);
v___x_2241_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2238_, v___x_2239_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23____boxed(lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_();
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2246_ = 1;
v___x_2247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_);
v___x_2248_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2245_, v___x_2246_, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25____boxed(lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_();
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object* v_e_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2261_ = ((lean_object*)(l_Int_reduceFMod___redArg___closed__1));
v___x_2262_ = lean_unsigned_to_nat(2u);
v___x_2263_ = l_Lean_Expr_isAppOfArity(v_e_2255_, v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = l_Lean_Expr_appFn_x21(v_e_2255_);
v___x_2267_ = l_Lean_Expr_appArg_x21(v___x_2266_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = l_Lean_Meta_getIntValue_x3f(v___x_2267_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2322_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2322_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2322_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
if (lean_obj_tag(v_a_2269_) == 1)
{
lean_object* v_val_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2317_; 
v_val_2273_ = lean_ctor_get(v_a_2269_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2269_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2275_ = v_a_2269_;
v_isShared_2276_ = v_isSharedCheck_2317_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_val_2273_);
lean_dec(v_a_2269_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2317_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = l_Lean_Expr_appArg_x21(v_e_2255_);
v___x_2278_ = l_Lean_Meta_getIntValue_x3f(v___x_2277_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2308_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2308_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2308_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___y_2284_; 
if (lean_obj_tag(v_a_2279_) == 1)
{
lean_object* v_val_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
lean_del_object(v___x_2271_);
v_val_2291_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v_a_2279_, 1);
v___x_2292_ = l_Int_fmod(v_val_2273_, v_val_2291_);
lean_dec(v_val_2291_);
lean_dec(v_val_2273_);
v___x_2293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2294_ = lean_int_dec_le(v___x_2293_, v___x_2292_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2296_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2298_ = lean_int_neg(v___x_2292_);
lean_dec(v___x_2292_);
v___x_2299_ = l_Int_toNat(v___x_2298_);
lean_dec(v___x_2298_);
v___x_2300_ = l_Lean_instToExprInt_mkNat(v___x_2299_);
v___x_2301_ = l_Lean_mkApp3(v___x_2295_, v___x_2296_, v___x_2297_, v___x_2300_);
v___y_2284_ = v___x_2301_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = l_Int_toNat(v___x_2292_);
lean_dec(v___x_2292_);
v___x_2303_ = l_Lean_instToExprInt_mkNat(v___x_2302_);
v___y_2284_ = v___x_2303_;
goto v___jp_2283_;
}
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_del_object(v___x_2281_);
lean_dec(v_a_2279_);
lean_del_object(v___x_2275_);
lean_dec(v_val_2273_);
v___x_2304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2304_);
v___x_2306_ = v___x_2271_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
v___jp_2283_:
{
lean_object* v___x_2286_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 0);
lean_ctor_set(v___x_2275_, 0, v___y_2284_);
v___x_2286_ = v___x_2275_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___y_2284_);
v___x_2286_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2286_);
v___x_2288_ = v___x_2281_;
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
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2275_);
lean_dec(v_val_2273_);
lean_del_object(v___x_2271_);
v_a_2309_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2278_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2278_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_dec(v_a_2269_);
v___x_2318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2318_);
v___x_2320_ = v___x_2271_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v_a_2323_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2268_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2268_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object* v_e_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Int_reduceFMod___redArg(v_e_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec_ref(v_e_2331_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object* v_e_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Int_reduceFMod___redArg(v_e_2338_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object* v_e_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Int_reduceFMod(v_e_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_e_2348_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2375_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2376_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2373_, v___x_2374_, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21____boxed(lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_();
return v_res_2378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2383_ = 1;
v___x_2384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_);
v___x_2385_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2382_, v___x_2383_, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23____boxed(lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_();
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2390_ = 1;
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_);
v___x_2392_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2389_, v___x_2390_, v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25____boxed(lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_();
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object* v_e_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__1));
v___x_2407_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__2));
v___x_2408_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v___x_2406_, v___x_2407_, v_e_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object* v_e_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Int_reduceBdiv___redArg(v_e_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec_ref(v_e_2409_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object* v_e_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Int_reduceBdiv___redArg(v_e_2416_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object* v_e_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Int_reduceBdiv(v_e_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_e_2426_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2453_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2454_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2451_, v___x_2452_, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21____boxed(lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_();
return v_res_2456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2461_ = 1;
v___x_2462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_);
v___x_2463_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2460_, v___x_2461_, v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23____boxed(lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_();
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2468_ = 1;
v___x_2469_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_);
v___x_2470_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2467_, v___x_2468_, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25____boxed(lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_();
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object* v_e_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__1));
v___x_2485_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__2));
v___x_2486_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v___x_2484_, v___x_2485_, v_e_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object* v_e_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Int_reduceBmod___redArg(v_e_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_e_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object* v_e_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Int_reduceBmod___redArg(v_e_2494_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Int_reduceBmod(v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_e_2504_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2531_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2532_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2529_, v___x_2530_, v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21____boxed(lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_();
return v_res_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2539_ = 1;
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_);
v___x_2541_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2538_, v___x_2539_, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23____boxed(lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_();
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2546_ = 1;
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_);
v___x_2548_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2545_, v___x_2546_, v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25____boxed(lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_();
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object* v_e_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2556_, v_a_2559_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = l_Lean_Expr_cleanupAnnotations(v_a_2567_);
v___x_2569_ = l_Lean_Expr_isApp(v___x_2568_);
if (v___x_2569_ == 0)
{
lean_dec_ref(v___x_2568_);
goto v___jp_2563_;
}
else
{
lean_object* v_arg_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_arg_2570_ = lean_ctor_get(v___x_2568_, 1);
lean_inc_ref(v_arg_2570_);
v___x_2571_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2568_);
v___x_2572_ = l_Lean_Expr_isApp(v___x_2571_);
if (v___x_2572_ == 0)
{
lean_dec_ref(v___x_2571_);
lean_dec_ref(v_arg_2570_);
goto v___jp_2563_;
}
else
{
lean_object* v_arg_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_arg_2573_ = lean_ctor_get(v___x_2571_, 1);
lean_inc_ref(v_arg_2573_);
v___x_2574_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2571_);
v___x_2575_ = l_Lean_Expr_isApp(v___x_2574_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v___x_2574_);
lean_dec_ref(v_arg_2573_);
lean_dec_ref(v_arg_2570_);
goto v___jp_2563_;
}
else
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2574_);
v___x_2577_ = l_Lean_Expr_isApp(v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v___x_2576_);
lean_dec_ref(v_arg_2573_);
lean_dec_ref(v_arg_2570_);
goto v___jp_2563_;
}
else
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2576_);
v___x_2579_ = l_Lean_Expr_isApp(v___x_2578_);
if (v___x_2579_ == 0)
{
lean_dec_ref(v___x_2578_);
lean_dec_ref(v_arg_2573_);
lean_dec_ref(v_arg_2570_);
goto v___jp_2563_;
}
else
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2578_);
v___x_2581_ = l_Lean_Expr_isApp(v___x_2580_);
if (v___x_2581_ == 0)
{
lean_dec_ref(v___x_2580_);
lean_dec_ref(v_arg_2573_);
lean_dec_ref(v_arg_2570_);
goto v___jp_2563_;
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2580_);
v___x_2583_ = ((lean_object*)(l_Int_reducePow___redArg___closed__2));
v___x_2584_ = l_Lean_Expr_isConstOf(v___x_2582_, v___x_2583_);
lean_dec_ref(v___x_2582_);
if (v___x_2584_ == 0)
{
lean_dec_ref(v_arg_2573_);
lean_dec_ref(v_arg_2570_);
goto v___jp_2563_;
}
else
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Meta_getIntValue_x3f(v_arg_2573_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2659_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2659_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2659_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
if (lean_obj_tag(v_a_2586_) == 1)
{
lean_object* v_val_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2588_);
v_val_2590_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v_a_2586_, 1);
v___x_2591_ = l_Lean_Meta_getNatValue_x3f(v_arg_2570_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec_ref(v_arg_2570_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2646_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2646_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2646_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
if (lean_obj_tag(v_a_2592_) == 1)
{
lean_object* v_config_2596_; lean_object* v_val_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2641_; 
v_config_2596_ = lean_ctor_get(v_a_2557_, 0);
v_val_2597_ = lean_ctor_get(v_a_2592_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_a_2592_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2599_ = v_a_2592_;
v_isShared_2600_ = v_isSharedCheck_2641_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_val_2597_);
lean_dec(v_a_2592_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2641_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
uint8_t v_warnExponents_2601_; lean_object* v___x_2602_; 
v_warnExponents_2601_ = lean_ctor_get_uint8(v_config_2596_, sizeof(void*)*3 + 25);
lean_inc(v_val_2597_);
v___x_2602_ = l_Lean_checkExponent(v_val_2597_, v_warnExponents_2601_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2632_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2632_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2632_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___y_2608_; uint8_t v___x_2615_; 
v___x_2615_ = lean_unbox(v_a_2603_);
lean_dec(v_a_2603_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_del_object(v___x_2605_);
lean_del_object(v___x_2599_);
lean_dec(v_val_2597_);
lean_dec(v_val_2590_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2616_);
v___x_2618_ = v___x_2594_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_del_object(v___x_2594_);
v___x_2620_ = l_Int_pow(v_val_2590_, v_val_2597_);
lean_dec(v_val_2597_);
lean_dec(v_val_2590_);
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2622_ = lean_int_dec_le(v___x_2621_, v___x_2620_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2626_ = lean_int_neg(v___x_2620_);
lean_dec(v___x_2620_);
v___x_2627_ = l_Int_toNat(v___x_2626_);
lean_dec(v___x_2626_);
v___x_2628_ = l_Lean_instToExprInt_mkNat(v___x_2627_);
v___x_2629_ = l_Lean_mkApp3(v___x_2623_, v___x_2624_, v___x_2625_, v___x_2628_);
v___y_2608_ = v___x_2629_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = l_Int_toNat(v___x_2620_);
lean_dec(v___x_2620_);
v___x_2631_ = l_Lean_instToExprInt_mkNat(v___x_2630_);
v___y_2608_ = v___x_2631_;
goto v___jp_2607_;
}
}
v___jp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set_tag(v___x_2599_, 0);
lean_ctor_set(v___x_2599_, 0, v___y_2608_);
v___x_2610_ = v___x_2599_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___y_2608_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2612_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2610_);
v___x_2612_ = v___x_2605_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_del_object(v___x_2599_);
lean_dec(v_val_2597_);
lean_del_object(v___x_2594_);
lean_dec(v_val_2590_);
v_a_2633_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2602_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2602_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_dec(v_a_2592_);
lean_dec(v_val_2590_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2642_);
v___x_2644_ = v___x_2594_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_val_2590_);
v_a_2647_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2591_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2591_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2657_; 
lean_dec(v_a_2586_);
lean_dec_ref(v_arg_2570_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2655_);
v___x_2657_ = v___x_2588_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v_arg_2570_);
v_a_2660_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2585_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2585_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
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
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2566_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2566_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
v___jp_2563_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object* v_e_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Int_reducePow___redArg(v_e_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec_ref(v_a_2677_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object* v_e_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Int_reducePow___redArg(v_e_2684_, v_a_2686_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object* v_e_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Int_reducePow(v_e_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2733_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2734_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2731_, v___x_2732_, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30____boxed(lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_();
return v_res_2736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2741_ = 1;
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_);
v___x_2743_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2740_, v___x_2741_, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32____boxed(lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_();
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_(){
_start:
{
lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2748_ = 1;
v___x_2749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_);
v___x_2750_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2747_, v___x_2748_, v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34____boxed(lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_();
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object* v_e_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = ((lean_object*)(l_Int_reduceLT___redArg___closed__2));
v___x_2765_ = lean_unsigned_to_nat(4u);
v___x_2766_ = l_Lean_Expr_isAppOfArity(v_e_2758_, v___x_2764_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec_ref(v_e_2758_);
v___x_2767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = l_Lean_Expr_appFn_x21(v_e_2758_);
v___x_2770_ = l_Lean_Expr_appArg_x21(v___x_2769_);
lean_dec_ref(v___x_2769_);
v___x_2771_ = l_Lean_Meta_getIntValue_x3f(v___x_2770_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2803_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2803_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2803_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
if (lean_obj_tag(v_a_2772_) == 1)
{
lean_object* v_val_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2774_);
v_val_2776_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v_a_2772_, 1);
v___x_2777_ = l_Lean_Expr_appArg_x21(v_e_2758_);
v___x_2778_ = l_Lean_Meta_getIntValue_x3f(v___x_2777_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2790_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
if (lean_obj_tag(v_a_2779_) == 1)
{
lean_object* v_val_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; 
lean_del_object(v___x_2781_);
v_val_2783_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v_a_2779_, 1);
v___x_2784_ = lean_int_dec_lt(v_val_2776_, v_val_2783_);
lean_dec(v_val_2783_);
lean_dec(v_val_2776_);
v___x_2785_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2758_, v___x_2784_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
return v___x_2785_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_dec(v_a_2779_);
lean_dec(v_val_2776_);
lean_dec_ref(v_e_2758_);
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2786_);
v___x_2788_ = v___x_2781_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_val_2776_);
lean_dec_ref(v_e_2758_);
v_a_2791_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2778_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2778_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_dec(v_a_2772_);
lean_dec_ref(v_e_2758_);
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2799_);
v___x_2801_ = v___x_2774_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v_e_2758_);
v_a_2804_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2771_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2771_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object* v_e_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Int_reduceLT___redArg(v_e_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object* v_e_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Int_reduceLT___redArg(v_e_2819_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object* v_e_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Int_reduceLT(v_e_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2859_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2860_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2857_, v___x_2858_, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27____boxed(lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_();
return v_res_2862_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2867_ = 1;
v___x_2868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_);
v___x_2869_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2866_, v___x_2867_, v___x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29____boxed(lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_();
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2874_ = 1;
v___x_2875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_);
v___x_2876_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2873_, v___x_2874_, v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31____boxed(lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_();
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object* v_e_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2890_ = ((lean_object*)(l_Int_reduceLE___redArg___closed__2));
v___x_2891_ = lean_unsigned_to_nat(4u);
v___x_2892_ = l_Lean_Expr_isAppOfArity(v_e_2884_, v___x_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref(v_e_2884_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = l_Lean_Expr_appFn_x21(v_e_2884_);
v___x_2896_ = l_Lean_Expr_appArg_x21(v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = l_Lean_Meta_getIntValue_x3f(v___x_2896_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2929_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2929_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2929_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
if (lean_obj_tag(v_a_2898_) == 1)
{
lean_object* v_val_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_del_object(v___x_2900_);
v_val_2902_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v_a_2898_, 1);
v___x_2903_ = l_Lean_Expr_appArg_x21(v_e_2884_);
v___x_2904_ = l_Lean_Meta_getIntValue_x3f(v___x_2903_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2916_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2916_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2916_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
if (lean_obj_tag(v_a_2905_) == 1)
{
lean_object* v_val_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; 
lean_del_object(v___x_2907_);
v_val_2909_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_val_2909_);
lean_dec_ref_known(v_a_2905_, 1);
v___x_2910_ = lean_int_dec_le(v_val_2902_, v_val_2909_);
lean_dec(v_val_2909_);
lean_dec(v_val_2902_);
v___x_2911_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2884_, v___x_2910_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_2911_;
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
lean_dec(v_a_2905_);
lean_dec(v_val_2902_);
lean_dec_ref(v_e_2884_);
v___x_2912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2912_);
v___x_2914_ = v___x_2907_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_val_2902_);
lean_dec_ref(v_e_2884_);
v_a_2917_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2904_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2904_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
lean_dec(v_a_2898_);
lean_dec_ref(v_e_2884_);
v___x_2925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2925_);
v___x_2927_ = v___x_2900_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v_e_2884_);
v_a_2930_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2897_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2897_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object* v_e_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Int_reduceLE___redArg(v_e_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object* v_e_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Int_reduceLE___redArg(v_e_2945_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object* v_e_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Int_reduceLE(v_e_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2985_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2986_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2983_, v___x_2984_, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27____boxed(lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_();
return v_res_2988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2993_ = 1;
v___x_2994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_);
v___x_2995_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2992_, v___x_2993_, v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29____boxed(lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_();
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3000_ = 1;
v___x_3001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_);
v___x_3002_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2999_, v___x_3000_, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31____boxed(lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_();
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object* v_e_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3016_ = ((lean_object*)(l_Int_reduceGT___redArg___closed__2));
v___x_3017_ = lean_unsigned_to_nat(4u);
v___x_3018_ = l_Lean_Expr_isAppOfArity(v_e_3010_, v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec_ref(v_e_3010_);
v___x_3019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = l_Lean_Expr_appFn_x21(v_e_3010_);
v___x_3022_ = l_Lean_Expr_appArg_x21(v___x_3021_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = l_Lean_Meta_getIntValue_x3f(v___x_3022_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3055_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3055_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3055_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
if (lean_obj_tag(v_a_3024_) == 1)
{
lean_object* v_val_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_del_object(v___x_3026_);
v_val_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v_a_3024_, 1);
v___x_3029_ = l_Lean_Expr_appArg_x21(v_e_3010_);
v___x_3030_ = l_Lean_Meta_getIntValue_x3f(v___x_3029_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3042_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3042_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3042_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
if (lean_obj_tag(v_a_3031_) == 1)
{
lean_object* v_val_3035_; uint8_t v___x_3036_; lean_object* v___x_3037_; 
lean_del_object(v___x_3033_);
v_val_3035_ = lean_ctor_get(v_a_3031_, 0);
lean_inc(v_val_3035_);
lean_dec_ref_known(v_a_3031_, 1);
v___x_3036_ = lean_int_dec_lt(v_val_3035_, v_val_3028_);
lean_dec(v_val_3028_);
lean_dec(v_val_3035_);
v___x_3037_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3010_, v___x_3036_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v___x_3037_;
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec(v_a_3031_);
lean_dec(v_val_3028_);
lean_dec_ref(v_e_3010_);
v___x_3038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3038_);
v___x_3040_ = v___x_3033_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_val_3028_);
lean_dec_ref(v_e_3010_);
v_a_3043_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3030_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3030_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
lean_dec(v_a_3024_);
lean_dec_ref(v_e_3010_);
v___x_3051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3051_);
v___x_3053_ = v___x_3026_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_e_3010_);
v_a_3056_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3023_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3023_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object* v_e_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Int_reduceGT___redArg(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object* v_e_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Int_reduceGT___redArg(v_e_3071_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object* v_e_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Int_reduceGT(v_e_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_3098_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3099_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3096_, v___x_3097_, v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27____boxed(lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_();
return v_res_3101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3106_ = 1;
v___x_3107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_);
v___x_3108_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3105_, v___x_3106_, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29____boxed(lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_();
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3113_ = 1;
v___x_3114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_);
v___x_3115_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3112_, v___x_3113_, v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31____boxed(lean_object* v_a_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_();
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object* v_e_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = ((lean_object*)(l_Int_reduceGE___redArg___closed__2));
v___x_3130_ = lean_unsigned_to_nat(4u);
v___x_3131_ = l_Lean_Expr_isAppOfArity(v_e_3123_, v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec_ref(v_e_3123_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = l_Lean_Expr_appFn_x21(v_e_3123_);
v___x_3135_ = l_Lean_Expr_appArg_x21(v___x_3134_);
lean_dec_ref(v___x_3134_);
v___x_3136_ = l_Lean_Meta_getIntValue_x3f(v___x_3135_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3168_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3168_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3168_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
if (lean_obj_tag(v_a_3137_) == 1)
{
lean_object* v_val_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_del_object(v___x_3139_);
v_val_3141_ = lean_ctor_get(v_a_3137_, 0);
lean_inc(v_val_3141_);
lean_dec_ref_known(v_a_3137_, 1);
v___x_3142_ = l_Lean_Expr_appArg_x21(v_e_3123_);
v___x_3143_ = l_Lean_Meta_getIntValue_x3f(v___x_3142_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3155_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3155_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3155_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
if (lean_obj_tag(v_a_3144_) == 1)
{
lean_object* v_val_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
lean_del_object(v___x_3146_);
v_val_3148_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_val_3148_);
lean_dec_ref_known(v_a_3144_, 1);
v___x_3149_ = lean_int_dec_le(v_val_3148_, v_val_3141_);
lean_dec(v_val_3141_);
lean_dec(v_val_3148_);
v___x_3150_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3123_, v___x_3149_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_dec(v_a_3144_);
lean_dec(v_val_3141_);
lean_dec_ref(v_e_3123_);
v___x_3151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3151_);
v___x_3153_ = v___x_3146_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
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
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_val_3141_);
lean_dec_ref(v_e_3123_);
v_a_3156_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3143_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3143_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_dec(v_a_3137_);
lean_dec_ref(v_e_3123_);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3164_);
v___x_3166_ = v___x_3139_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v_e_3123_);
v_a_3169_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3136_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3136_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object* v_e_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Int_reduceGE___redArg(v_e_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object* v_e_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Int_reduceGE___redArg(v_e_3184_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object* v_e_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Int_reduceGE(v_e_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3211_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3212_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3209_, v___x_3210_, v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27____boxed(lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_();
return v_res_3214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3218_; uint8_t v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3219_ = 1;
v___x_3220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_);
v___x_3221_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3218_, v___x_3219_, v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29____boxed(lean_object* v_a_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_();
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3226_ = 1;
v___x_3227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_);
v___x_3228_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3225_, v___x_3226_, v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31____boxed(lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_();
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object* v_e_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3240_ = ((lean_object*)(l_Int_reduceEq___redArg___closed__1));
v___x_3241_ = lean_unsigned_to_nat(3u);
v___x_3242_ = l_Lean_Expr_isAppOfArity(v_e_3234_, v___x_3240_, v___x_3241_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_dec_ref(v_e_3234_);
v___x_3243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = l_Lean_Expr_appFn_x21(v_e_3234_);
v___x_3246_ = l_Lean_Expr_appArg_x21(v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = l_Lean_Meta_getIntValue_x3f(v___x_3246_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3279_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3279_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3279_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
if (lean_obj_tag(v_a_3248_) == 1)
{
lean_object* v_val_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_del_object(v___x_3250_);
v_val_3252_ = lean_ctor_get(v_a_3248_, 0);
lean_inc(v_val_3252_);
lean_dec_ref_known(v_a_3248_, 1);
v___x_3253_ = l_Lean_Expr_appArg_x21(v_e_3234_);
v___x_3254_ = l_Lean_Meta_getIntValue_x3f(v___x_3253_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3266_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3266_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3266_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
if (lean_obj_tag(v_a_3255_) == 1)
{
lean_object* v_val_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; 
lean_del_object(v___x_3257_);
v_val_3259_ = lean_ctor_get(v_a_3255_, 0);
lean_inc(v_val_3259_);
lean_dec_ref_known(v_a_3255_, 1);
v___x_3260_ = lean_int_dec_eq(v_val_3252_, v_val_3259_);
lean_dec(v_val_3259_);
lean_dec(v_val_3252_);
v___x_3261_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3234_, v___x_3260_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_dec(v_a_3255_);
lean_dec(v_val_3252_);
lean_dec_ref(v_e_3234_);
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3262_);
v___x_3264_ = v___x_3257_;
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
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_val_3252_);
lean_dec_ref(v_e_3234_);
v_a_3267_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3254_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3254_);
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
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
lean_dec(v_a_3248_);
lean_dec_ref(v_e_3234_);
v___x_3275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3275_);
v___x_3277_ = v___x_3250_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v_e_3234_);
v_a_3280_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3247_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3247_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object* v_e_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Int_reduceEq___redArg(v_e_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object* v_e_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Int_reduceEq___redArg(v_e_3295_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object* v_e_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Int_reduceEq(v_e_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3334_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3335_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3332_, v___x_3333_, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27____boxed(lean_object* v_a_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_();
return v_res_3337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3342_ = 1;
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_);
v___x_3344_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3341_, v___x_3342_, v___x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29____boxed(lean_object* v_a_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_();
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3348_; uint8_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3349_ = 1;
v___x_3350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_);
v___x_3351_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3348_, v___x_3349_, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31____boxed(lean_object* v_a_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_();
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object* v_e_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3363_ = ((lean_object*)(l_Int_reduceNe___redArg___closed__1));
v___x_3364_ = lean_unsigned_to_nat(3u);
v___x_3365_ = l_Lean_Expr_isAppOfArity(v_e_3357_, v___x_3363_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec_ref(v_e_3357_);
v___x_3366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
return v___x_3367_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = l_Lean_Expr_appFn_x21(v_e_3357_);
v___x_3369_ = l_Lean_Expr_appArg_x21(v___x_3368_);
lean_dec_ref(v___x_3368_);
v___x_3370_ = l_Lean_Meta_getIntValue_x3f(v___x_3369_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3404_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3404_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3404_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
if (lean_obj_tag(v_a_3371_) == 1)
{
lean_object* v_val_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_del_object(v___x_3373_);
v_val_3375_ = lean_ctor_get(v_a_3371_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v_a_3371_, 1);
v___x_3376_ = l_Lean_Expr_appArg_x21(v_e_3357_);
v___x_3377_ = l_Lean_Meta_getIntValue_x3f(v___x_3376_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3391_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3391_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3391_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
if (lean_obj_tag(v_a_3378_) == 1)
{
lean_object* v_val_3382_; uint8_t v___x_3383_; 
lean_del_object(v___x_3380_);
v_val_3382_ = lean_ctor_get(v_a_3378_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_a_3378_, 1);
v___x_3383_ = lean_int_dec_eq(v_val_3375_, v_val_3382_);
lean_dec(v_val_3382_);
lean_dec(v_val_3375_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3357_, v___x_3365_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
return v___x_3384_;
}
else
{
uint8_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = 0;
v___x_3386_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3357_, v___x_3385_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
return v___x_3386_;
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
lean_dec(v_a_3378_);
lean_dec(v_val_3375_);
lean_dec_ref(v_e_3357_);
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3387_);
v___x_3389_ = v___x_3380_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v_val_3375_);
lean_dec_ref(v_e_3357_);
v_a_3392_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3377_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3377_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
lean_dec(v_a_3371_);
lean_dec_ref(v_e_3357_);
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3400_);
v___x_3402_ = v___x_3373_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec_ref(v_e_3357_);
v_a_3405_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3370_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3370_);
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
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object* v_e_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Int_reduceNe___redArg(v_e_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object* v_e_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Int_reduceNe___redArg(v_e_3420_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object* v_e_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Int_reduceNe(v_e_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
lean_dec(v_a_3431_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3464_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3465_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3462_, v___x_3463_, v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27____boxed(lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_();
return v_res_3467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3472_ = 1;
v___x_3473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_);
v___x_3474_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3471_, v___x_3472_, v___x_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29____boxed(lean_object* v_a_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_();
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3479_ = 1;
v___x_3480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_);
v___x_3481_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3478_, v___x_3479_, v___x_3480_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31____boxed(lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_();
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object* v_e_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3495_ = ((lean_object*)(l_Int_reduceBEq___redArg___closed__2));
v___x_3496_ = lean_unsigned_to_nat(4u);
v___x_3497_ = l_Lean_Expr_isAppOfArity(v_e_3489_, v___x_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = l_Lean_Expr_appFn_x21(v_e_3489_);
v___x_3501_ = l_Lean_Expr_appArg_x21(v___x_3500_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = l_Lean_Meta_getIntValue_x3f(v___x_3501_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3547_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3547_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3547_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
if (lean_obj_tag(v_a_3503_) == 1)
{
lean_object* v_val_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3542_; 
v_val_3507_ = lean_ctor_get(v_a_3503_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_a_3503_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3509_ = v_a_3503_;
v_isShared_3510_ = v_isSharedCheck_3542_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_val_3507_);
lean_dec(v_a_3503_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3542_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = l_Lean_Expr_appArg_x21(v_e_3489_);
v___x_3512_ = l_Lean_Meta_getIntValue_x3f(v___x_3511_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3533_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3533_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3533_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___y_3518_; 
if (lean_obj_tag(v_a_3513_) == 1)
{
lean_object* v_val_3525_; uint8_t v___x_3526_; 
lean_del_object(v___x_3505_);
v_val_3525_ = lean_ctor_get(v_a_3513_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v_a_3513_, 1);
v___x_3526_ = lean_int_dec_eq(v_val_3507_, v_val_3525_);
lean_dec(v_val_3525_);
lean_dec(v_val_3507_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_3518_ = v___x_3527_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_3518_ = v___x_3528_;
goto v___jp_3517_;
}
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_del_object(v___x_3515_);
lean_dec(v_a_3513_);
lean_del_object(v___x_3509_);
lean_dec(v_val_3507_);
v___x_3529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3529_);
v___x_3531_ = v___x_3505_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
v___jp_3517_:
{
lean_object* v___x_3520_; 
lean_inc_ref(v___y_3518_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set_tag(v___x_3509_, 0);
lean_ctor_set(v___x_3509_, 0, v___y_3518_);
v___x_3520_ = v___x_3509_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___y_3518_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3520_);
v___x_3522_ = v___x_3515_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_del_object(v___x_3509_);
lean_dec(v_val_3507_);
lean_del_object(v___x_3505_);
v_a_3534_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3512_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3512_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
lean_dec(v_a_3503_);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3543_);
v___x_3545_ = v___x_3505_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3502_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3502_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object* v_e_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Int_reduceBEq___redArg(v_e_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec_ref(v_e_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object* v_e_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Int_reduceBEq___redArg(v_e_3563_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object* v_e_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Int_reduceBEq(v_e_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_e_3573_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3603_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3604_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3601_, v___x_3602_, v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27____boxed(lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_();
return v_res_3606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3611_ = 1;
v___x_3612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_);
v___x_3613_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3610_, v___x_3611_, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29____boxed(lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_();
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3617_; uint8_t v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3618_ = 1;
v___x_3619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_);
v___x_3620_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3617_, v___x_3618_, v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31____boxed(lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_();
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object* v_e_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3632_ = ((lean_object*)(l_Int_reduceBNe___redArg___closed__1));
v___x_3633_ = lean_unsigned_to_nat(4u);
v___x_3634_ = l_Lean_Expr_isAppOfArity(v_e_3626_, v___x_3632_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = l_Lean_Expr_appFn_x21(v_e_3626_);
v___x_3638_ = l_Lean_Expr_appArg_x21(v___x_3637_);
lean_dec_ref(v___x_3637_);
v___x_3639_ = l_Lean_Meta_getIntValue_x3f(v___x_3638_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3685_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3685_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3685_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
if (lean_obj_tag(v_a_3640_) == 1)
{
lean_object* v_val_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3680_; 
v_val_3644_ = lean_ctor_get(v_a_3640_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_a_3640_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3646_ = v_a_3640_;
v_isShared_3647_ = v_isSharedCheck_3680_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_val_3644_);
lean_dec(v_a_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3680_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = l_Lean_Expr_appArg_x21(v_e_3626_);
v___x_3649_ = l_Lean_Meta_getIntValue_x3f(v___x_3648_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3671_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3671_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3671_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___y_3655_; 
if (lean_obj_tag(v_a_3650_) == 1)
{
lean_object* v_val_3664_; uint8_t v___x_3665_; 
lean_del_object(v___x_3642_);
v_val_3664_ = lean_ctor_get(v_a_3650_, 0);
lean_inc(v_val_3664_);
lean_dec_ref_known(v_a_3650_, 1);
v___x_3665_ = lean_int_dec_eq(v_val_3644_, v_val_3664_);
lean_dec(v_val_3664_);
lean_dec(v_val_3644_);
if (v___x_3665_ == 0)
{
if (v___x_3634_ == 0)
{
goto v___jp_3662_;
}
else
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_3655_ = v___x_3666_;
goto v___jp_3654_;
}
}
else
{
goto v___jp_3662_;
}
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
lean_del_object(v___x_3652_);
lean_dec(v_a_3650_);
lean_del_object(v___x_3646_);
lean_dec(v_val_3644_);
v___x_3667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3667_);
v___x_3669_ = v___x_3642_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
v___jp_3654_:
{
lean_object* v___x_3657_; 
lean_inc_ref(v___y_3655_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 0);
lean_ctor_set(v___x_3646_, 0, v___y_3655_);
v___x_3657_ = v___x_3646_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___y_3655_);
v___x_3657_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3659_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3657_);
v___x_3659_ = v___x_3652_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
v___jp_3662_:
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_3655_ = v___x_3663_;
goto v___jp_3654_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_del_object(v___x_3646_);
lean_dec(v_val_3644_);
lean_del_object(v___x_3642_);
v_a_3672_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3649_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3649_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
lean_dec(v_a_3640_);
v___x_3681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3681_);
v___x_3683_ = v___x_3642_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3639_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3639_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object* v_e_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Int_reduceBNe___redArg(v_e_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec_ref(v_e_3694_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object* v_e_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Int_reduceBNe___redArg(v_e_3701_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object* v_e_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Int_reduceBNe(v_e_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_e_3711_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3741_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3742_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3739_, v___x_3740_, v___x_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27____boxed(lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_();
return v_res_3744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3748_; uint8_t v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3749_ = 1;
v___x_3750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_);
v___x_3751_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3748_, v___x_3749_, v___x_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29____boxed(lean_object* v_a_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_();
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3756_ = 1;
v___x_3757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_);
v___x_3758_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3755_, v___x_3756_, v___x_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31____boxed(lean_object* v_a_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_();
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(lean_object* v_declName_3761_, lean_object* v_op_3762_, lean_object* v_e_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = lean_unsigned_to_nat(1u);
v___x_3770_ = l_Lean_Expr_isAppOfArity(v_e_3763_, v_declName_3761_, v___x_3769_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_dec_ref(v_op_3762_);
v___x_3771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = l_Lean_Expr_appArg_x21(v_e_3763_);
v___x_3774_ = l_Lean_Meta_getIntValue_x3f(v___x_3773_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3796_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3777_ = v___x_3774_;
v_isShared_3778_ = v_isSharedCheck_3796_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3796_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
if (lean_obj_tag(v_a_3775_) == 1)
{
lean_object* v_val_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3791_; 
v_val_3779_ = lean_ctor_get(v_a_3775_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3775_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3781_ = v_a_3775_;
v_isShared_3782_ = v_isSharedCheck_3791_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_val_3779_);
lean_dec(v_a_3775_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3791_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3783_ = lean_apply_1(v_op_3762_, v_val_3779_);
v___x_3784_ = l_Lean_mkNatLit(v___x_3783_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set_tag(v___x_3781_, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3784_);
v___x_3786_ = v___x_3781_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 0, v___x_3786_);
v___x_3788_ = v___x_3777_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_dec(v_a_3775_);
lean_dec_ref(v_op_3762_);
v___x_3792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 0, v___x_3792_);
v___x_3794_ = v___x_3777_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_op_3762_);
v_a_3797_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3774_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3774_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg___boxed(lean_object* v_declName_3805_, lean_object* v_op_3806_, lean_object* v_e_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(v_declName_3805_, v_op_3806_, v_e_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec_ref(v_e_3807_);
lean_dec(v_declName_3805_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(lean_object* v_declName_3814_, lean_object* v_op_3815_, lean_object* v_e_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_){
_start:
{
lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3825_ = lean_unsigned_to_nat(1u);
v___x_3826_ = l_Lean_Expr_isAppOfArity(v_e_3816_, v_declName_3814_, v___x_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_dec_ref(v_op_3815_);
v___x_3827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
return v___x_3828_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = l_Lean_Expr_appArg_x21(v_e_3816_);
v___x_3830_ = l_Lean_Meta_getIntValue_x3f(v___x_3829_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3852_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3852_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3852_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
if (lean_obj_tag(v_a_3831_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3847_; 
v_val_3835_ = lean_ctor_get(v_a_3831_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_a_3831_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3837_ = v_a_3831_;
v_isShared_3838_ = v_isSharedCheck_3847_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_val_3835_);
lean_dec(v_a_3831_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3847_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3839_ = lean_apply_1(v_op_3815_, v_val_3835_);
v___x_3840_ = l_Lean_mkNatLit(v___x_3839_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3840_);
v___x_3842_ = v___x_3837_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3844_; 
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3842_);
v___x_3844_ = v___x_3833_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec(v_a_3831_);
lean_dec_ref(v_op_3815_);
v___x_3848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3848_);
v___x_3850_ = v___x_3833_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec_ref(v_op_3815_);
v_a_3853_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3830_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3830_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___boxed(lean_object* v_declName_3861_, lean_object* v_op_3862_, lean_object* v_e_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(v_declName_3861_, v_op_3862_, v_e_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_e_3863_);
lean_dec(v_declName_3861_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object* v_e_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3883_ = ((lean_object*)(l_Int_reduceAbs___redArg___closed__1));
v___x_3884_ = lean_unsigned_to_nat(1u);
v___x_3885_ = l_Lean_Expr_isAppOfArity(v_e_3877_, v___x_3883_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = l_Lean_Expr_appArg_x21(v_e_3877_);
v___x_3889_ = l_Lean_Meta_getIntValue_x3f(v___x_3888_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3911_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3911_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3911_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
if (lean_obj_tag(v_a_3890_) == 1)
{
lean_object* v_val_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3906_; 
v_val_3894_ = lean_ctor_get(v_a_3890_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_a_3890_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3896_ = v_a_3890_;
v_isShared_3897_ = v_isSharedCheck_3906_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_val_3894_);
lean_dec(v_a_3890_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3906_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3898_ = lean_nat_abs(v_val_3894_);
lean_dec(v_val_3894_);
v___x_3899_ = l_Lean_mkNatLit(v___x_3898_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set_tag(v___x_3896_, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3899_);
v___x_3901_ = v___x_3896_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3903_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3901_);
v___x_3903_ = v___x_3892_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
lean_dec(v_a_3890_);
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3907_);
v___x_3909_ = v___x_3892_;
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
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
v_a_3912_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3889_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3889_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object* v_e_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Int_reduceAbs___redArg(v_e_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec_ref(v_e_3920_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object* v_e_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Int_reduceAbs___redArg(v_e_3927_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object* v_e_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Int_reduceAbs(v_e_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_e_3937_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3963_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3964_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3961_, v___x_3962_, v___x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20____boxed(lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_();
return v_res_3966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3971_ = 1;
v___x_3972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_);
v___x_3973_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3970_, v___x_3971_, v___x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22____boxed(lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_();
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3978_ = 1;
v___x_3979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_);
v___x_3980_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3977_, v___x_3978_, v___x_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24____boxed(lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_();
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object* v_e_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v___x_3993_ = ((lean_object*)(l_Int_reduceToNat___redArg___closed__1));
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = l_Lean_Expr_isAppOfArity(v_e_3987_, v___x_3993_, v___x_3994_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
return v___x_3997_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = l_Lean_Expr_appArg_x21(v_e_3987_);
v___x_3999_ = l_Lean_Meta_getIntValue_x3f(v___x_3998_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4021_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4021_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4021_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
if (lean_obj_tag(v_a_4000_) == 1)
{
lean_object* v_val_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4016_; 
v_val_4004_ = lean_ctor_get(v_a_4000_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v_a_4000_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4006_ = v_a_4000_;
v_isShared_4007_ = v_isSharedCheck_4016_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_val_4004_);
lean_dec(v_a_4000_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4016_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4008_ = l_Int_toNat(v_val_4004_);
lean_dec(v_val_4004_);
v___x_4009_ = l_Lean_mkNatLit(v___x_4008_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set_tag(v___x_4006_, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4009_);
v___x_4011_ = v___x_4006_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4013_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v___x_4011_);
v___x_4013_ = v___x_4002_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
lean_dec(v_a_4000_);
v___x_4017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v___x_4017_);
v___x_4019_ = v___x_4002_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4017_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
v_a_4022_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_3999_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_3999_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object* v_e_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Int_reduceToNat___redArg(v_e_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec_ref(v_e_4030_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object* v_e_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Int_reduceToNat___redArg(v_e_4037_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object* v_e_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Int_reduceToNat(v_e_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4047_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4073_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4074_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4071_, v___x_4072_, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20____boxed(lean_object* v_a_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_();
return v_res_4076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4081_ = 1;
v___x_4082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_);
v___x_4083_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4080_, v___x_4081_, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22____boxed(lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_();
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4087_; uint8_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4088_ = 1;
v___x_4089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_);
v___x_4090_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4087_, v___x_4088_, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24____boxed(lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_();
return v_res_4092_;
}
}
static lean_object* _init_l_Int_reduceNegSucc___redArg___closed__2(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = lean_unsigned_to_nat(1u);
v___x_4098_ = lean_nat_to_int(v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object* v_e_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4099_, v_a_4101_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4159_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4159_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4159_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; uint8_t v___x_4114_; 
v___x_4113_ = l_Lean_Expr_cleanupAnnotations(v_a_4109_);
v___x_4114_ = l_Lean_Expr_isApp(v___x_4113_);
if (v___x_4114_ == 0)
{
lean_dec_ref(v___x_4113_);
lean_del_object(v___x_4111_);
goto v___jp_4105_;
}
else
{
lean_object* v_arg_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
v_arg_4115_ = lean_ctor_get(v___x_4113_, 1);
lean_inc_ref(v_arg_4115_);
v___x_4116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4113_);
v___x_4117_ = ((lean_object*)(l_Int_reduceNegSucc___redArg___closed__1));
v___x_4118_ = l_Lean_Expr_isConstOf(v___x_4116_, v___x_4117_);
lean_dec_ref(v___x_4116_);
if (v___x_4118_ == 0)
{
lean_dec_ref(v_arg_4115_);
lean_del_object(v___x_4111_);
goto v___jp_4105_;
}
else
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_Meta_getNatValue_x3f(v_arg_4115_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec_ref(v_arg_4115_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4150_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4150_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4150_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___y_4125_; 
if (lean_obj_tag(v_a_4120_) == 1)
{
lean_object* v_val_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
lean_del_object(v___x_4111_);
v_val_4130_ = lean_ctor_get(v_a_4120_, 0);
lean_inc(v_val_4130_);
lean_dec_ref_known(v_a_4120_, 1);
v___x_4131_ = lean_nat_to_int(v_val_4130_);
v___x_4132_ = lean_obj_once(&l_Int_reduceNegSucc___redArg___closed__2, &l_Int_reduceNegSucc___redArg___closed__2_once, _init_l_Int_reduceNegSucc___redArg___closed__2);
v___x_4133_ = lean_int_add(v___x_4131_, v___x_4132_);
lean_dec(v___x_4131_);
v___x_4134_ = lean_int_neg(v___x_4133_);
lean_dec(v___x_4133_);
v___x_4135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4136_ = lean_int_dec_le(v___x_4135_, v___x_4134_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4137_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4140_ = lean_int_neg(v___x_4134_);
lean_dec(v___x_4134_);
v___x_4141_ = l_Int_toNat(v___x_4140_);
lean_dec(v___x_4140_);
v___x_4142_ = l_Lean_instToExprInt_mkNat(v___x_4141_);
v___x_4143_ = l_Lean_mkApp3(v___x_4137_, v___x_4138_, v___x_4139_, v___x_4142_);
v___y_4125_ = v___x_4143_;
goto v___jp_4124_;
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = l_Int_toNat(v___x_4134_);
lean_dec(v___x_4134_);
v___x_4145_ = l_Lean_instToExprInt_mkNat(v___x_4144_);
v___y_4125_ = v___x_4145_;
goto v___jp_4124_;
}
}
else
{
lean_object* v___x_4146_; lean_object* v___x_4148_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
v___x_4146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v___x_4146_);
v___x_4148_ = v___x_4111_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
v___jp_4124_:
{
lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___y_4125_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v___x_4126_);
v___x_4128_ = v___x_4122_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_del_object(v___x_4111_);
v_a_4151_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4119_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4119_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
v_a_4160_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4108_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4108_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
v___jp_4105_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
return v___x_4107_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object* v_e_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Int_reduceNegSucc___redArg(v_e_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object* v_e_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Int_reduceNegSucc___redArg(v_e_4175_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object* v_e_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Int_reduceNegSucc(v_e_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4211_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4212_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4209_, v___x_4210_, v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20____boxed(lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_();
return v_res_4214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4218_; uint8_t v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4219_ = 1;
v___x_4220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_);
v___x_4221_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4218_, v___x_4219_, v___x_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22____boxed(lean_object* v_a_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_();
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4225_; uint8_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4226_ = 1;
v___x_4227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_);
v___x_4228_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4225_, v___x_4226_, v___x_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24____boxed(lean_object* v_a_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_();
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object* v_e_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4234_, v_a_4236_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4291_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4291_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4291_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; uint8_t v___x_4249_; 
v___x_4248_ = l_Lean_Expr_cleanupAnnotations(v_a_4244_);
v___x_4249_ = l_Lean_Expr_isApp(v___x_4248_);
if (v___x_4249_ == 0)
{
lean_dec_ref(v___x_4248_);
lean_del_object(v___x_4246_);
goto v___jp_4240_;
}
else
{
lean_object* v_arg_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; 
v_arg_4250_ = lean_ctor_get(v___x_4248_, 1);
lean_inc_ref(v_arg_4250_);
v___x_4251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4248_);
v___x_4252_ = ((lean_object*)(l_Int_reduceOfNat___redArg___closed__0));
v___x_4253_ = l_Lean_Expr_isConstOf(v___x_4251_, v___x_4252_);
lean_dec_ref(v___x_4251_);
if (v___x_4253_ == 0)
{
lean_dec_ref(v_arg_4250_);
lean_del_object(v___x_4246_);
goto v___jp_4240_;
}
else
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_Meta_getNatValue_x3f(v_arg_4250_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
lean_dec_ref(v_arg_4250_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4282_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4257_ = v___x_4254_;
v_isShared_4258_ = v_isSharedCheck_4282_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4254_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4282_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___y_4260_; 
if (lean_obj_tag(v_a_4255_) == 1)
{
lean_object* v_val_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; 
lean_del_object(v___x_4246_);
v_val_4265_ = lean_ctor_get(v_a_4255_, 0);
lean_inc(v_val_4265_);
lean_dec_ref_known(v_a_4255_, 1);
v___x_4266_ = lean_nat_to_int(v_val_4265_);
v___x_4267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4268_ = lean_int_dec_le(v___x_4267_, v___x_4266_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4272_ = lean_int_neg(v___x_4266_);
lean_dec(v___x_4266_);
v___x_4273_ = l_Int_toNat(v___x_4272_);
lean_dec(v___x_4272_);
v___x_4274_ = l_Lean_instToExprInt_mkNat(v___x_4273_);
v___x_4275_ = l_Lean_mkApp3(v___x_4269_, v___x_4270_, v___x_4271_, v___x_4274_);
v___y_4260_ = v___x_4275_;
goto v___jp_4259_;
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = l_Int_toNat(v___x_4266_);
lean_dec(v___x_4266_);
v___x_4277_ = l_Lean_instToExprInt_mkNat(v___x_4276_);
v___y_4260_ = v___x_4277_;
goto v___jp_4259_;
}
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4280_; 
lean_del_object(v___x_4257_);
lean_dec(v_a_4255_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4278_);
v___x_4280_ = v___x_4246_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
v___jp_4259_:
{
lean_object* v___x_4261_; lean_object* v___x_4263_; 
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___y_4260_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4261_);
v___x_4263_ = v___x_4257_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_del_object(v___x_4246_);
v_a_4283_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4254_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4254_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4243_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4243_);
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
v___jp_4240_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object* v_e_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Int_reduceOfNat___redArg(v_e_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object* v_e_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Int_reduceOfNat___redArg(v_e_4307_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object* v_e_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Int_reduceOfNat(v_e_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4343_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4344_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4341_, v___x_4342_, v___x_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20____boxed(lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_();
return v_res_4346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4350_; uint8_t v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4351_ = 1;
v___x_4352_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_);
v___x_4353_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4350_, v___x_4351_, v___x_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22____boxed(lean_object* v_a_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_();
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4358_ = 1;
v___x_4359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_);
v___x_4360_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4357_, v___x_4358_, v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24____boxed(lean_object* v_a_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_();
return v_res_4362_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = lean_box(0);
v___x_4373_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__4));
v___x_4374_ = l_Lean_mkConst(v___x_4373_, v___x_4372_);
return v___x_4374_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4378_ = lean_box(0);
v___x_4379_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__7));
v___x_4380_ = l_Lean_mkConst(v___x_4379_, v___x_4378_);
return v___x_4380_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4385_ = lean_box(0);
v___x_4386_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__10));
v___x_4387_ = l_Lean_mkConst(v___x_4386_, v___x_4385_);
return v___x_4387_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__14(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4391_ = lean_box(0);
v___x_4392_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__13));
v___x_4393_ = l_Lean_mkConst(v___x_4392_, v___x_4391_);
return v___x_4393_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__17(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_box(0);
v___x_4399_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__16));
v___x_4400_ = l_Lean_mkConst(v___x_4399_, v___x_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object* v_e_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4401_, v_a_4403_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l_Lean_Expr_cleanupAnnotations(v_a_4411_);
v___x_4413_ = l_Lean_Expr_isApp(v___x_4412_);
if (v___x_4413_ == 0)
{
lean_dec_ref(v___x_4412_);
goto v___jp_4407_;
}
else
{
lean_object* v_arg_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_arg_4414_ = lean_ctor_get(v___x_4412_, 1);
lean_inc_ref(v_arg_4414_);
v___x_4415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4412_);
v___x_4416_ = l_Lean_Expr_isApp(v___x_4415_);
if (v___x_4416_ == 0)
{
lean_dec_ref(v___x_4415_);
lean_dec_ref(v_arg_4414_);
goto v___jp_4407_;
}
else
{
lean_object* v_arg_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; 
v_arg_4417_ = lean_ctor_get(v___x_4415_, 1);
lean_inc_ref(v_arg_4417_);
v___x_4418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4415_);
v___x_4419_ = l_Lean_Expr_isApp(v___x_4418_);
if (v___x_4419_ == 0)
{
lean_dec_ref(v___x_4418_);
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
goto v___jp_4407_;
}
else
{
lean_object* v_arg_4420_; lean_object* v___x_4421_; uint8_t v___x_4422_; 
v_arg_4420_ = lean_ctor_get(v___x_4418_, 1);
lean_inc_ref(v_arg_4420_);
v___x_4421_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4418_);
v___x_4422_ = l_Lean_Expr_isApp(v___x_4421_);
if (v___x_4422_ == 0)
{
lean_dec_ref(v___x_4421_);
lean_dec_ref(v_arg_4420_);
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
goto v___jp_4407_;
}
else
{
lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4423_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4421_);
v___x_4424_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__2));
v___x_4425_ = l_Lean_Expr_isConstOf(v___x_4423_, v___x_4424_);
lean_dec_ref(v___x_4423_);
if (v___x_4425_ == 0)
{
lean_dec_ref(v_arg_4420_);
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
goto v___jp_4407_;
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__5, &l_Int_reduceDvd___redArg___closed__5_once, _init_l_Int_reduceDvd___redArg___closed__5);
v___x_4427_ = l_Lean_Meta_matchesInstance(v_arg_4420_, v___x_4426_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4514_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4514_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4514_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
uint8_t v___x_4432_; 
v___x_4432_ = lean_unbox(v_a_4428_);
lean_dec(v_a_4428_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; lean_object* v___x_4435_; 
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
v___x_4433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4433_);
v___x_4435_ = v___x_4430_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
else
{
lean_object* v___x_4437_; 
lean_del_object(v___x_4430_);
lean_inc_ref(v_arg_4417_);
v___x_4437_ = l_Lean_Meta_getIntValue_x3f(v_arg_4417_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4505_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4440_ = v___x_4437_;
v_isShared_4441_ = v_isSharedCheck_4505_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4505_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
if (lean_obj_tag(v_a_4438_) == 1)
{
lean_object* v_val_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4500_; 
lean_del_object(v___x_4440_);
v_val_4442_ = lean_ctor_get(v_a_4438_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_a_4438_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4444_ = v_a_4438_;
v_isShared_4445_ = v_isSharedCheck_4500_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_val_4442_);
lean_dec(v_a_4438_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4500_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; 
lean_inc_ref(v_arg_4414_);
v___x_4446_ = l_Lean_Meta_getIntValue_x3f(v_arg_4414_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4491_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4491_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4491_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
if (lean_obj_tag(v_a_4447_) == 1)
{
lean_object* v_val_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4486_; 
v_val_4451_ = lean_ctor_get(v_a_4447_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_a_4447_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4453_ = v_a_4447_;
v_isShared_4454_ = v_isSharedCheck_4486_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_val_4451_);
lean_dec(v_a_4447_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4486_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4455_ = lean_int_emod(v_val_4451_, v_val_4442_);
lean_dec(v_val_4442_);
lean_dec(v_val_4451_);
v___x_4456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4457_ = lean_int_dec_eq(v___x_4455_, v___x_4456_);
lean_dec(v___x_4455_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4463_; 
v___x_4458_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__8, &l_Int_reduceDvd___redArg___closed__8_once, _init_l_Int_reduceDvd___redArg___closed__8);
v___x_4459_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__11, &l_Int_reduceDvd___redArg___closed__11_once, _init_l_Int_reduceDvd___redArg___closed__11);
v___x_4460_ = l_Lean_eagerReflBoolTrue;
v___x_4461_ = l_Lean_mkApp3(v___x_4459_, v_arg_4417_, v_arg_4414_, v___x_4460_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4461_);
v___x_4463_ = v___x_4453_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4464_, 0, v___x_4458_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
lean_ctor_set_uint8(v___x_4464_, sizeof(void*)*2, v___x_4425_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set_tag(v___x_4444_, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4464_);
v___x_4466_ = v___x_4444_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4468_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4466_);
v___x_4468_ = v___x_4449_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
v___x_4472_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__14, &l_Int_reduceDvd___redArg___closed__14_once, _init_l_Int_reduceDvd___redArg___closed__14);
v___x_4473_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__17, &l_Int_reduceDvd___redArg___closed__17_once, _init_l_Int_reduceDvd___redArg___closed__17);
v___x_4474_ = l_Lean_eagerReflBoolTrue;
v___x_4475_ = l_Lean_mkApp3(v___x_4473_, v_arg_4417_, v_arg_4414_, v___x_4474_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4475_);
v___x_4477_ = v___x_4453_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4478_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4478_, 0, v___x_4472_);
lean_ctor_set(v___x_4478_, 1, v___x_4477_);
lean_ctor_set_uint8(v___x_4478_, sizeof(void*)*2, v___x_4425_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set_tag(v___x_4444_, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4478_);
v___x_4480_ = v___x_4444_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4482_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4480_);
v___x_4482_ = v___x_4449_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
lean_dec(v_a_4447_);
lean_del_object(v___x_4444_);
lean_dec(v_val_4442_);
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
v___x_4487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4487_);
v___x_4489_ = v___x_4449_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_del_object(v___x_4444_);
lean_dec(v_val_4442_);
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
v_a_4492_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4446_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4446_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_dec(v_a_4438_);
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
v___x_4501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4501_);
v___x_4503_ = v___x_4440_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
v_a_4506_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4437_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4437_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref(v_arg_4417_);
lean_dec_ref(v_arg_4414_);
v_a_4515_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4427_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4427_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
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
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
v_a_4523_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4410_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4410_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
v___jp_4407_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
return v___x_4409_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object* v_e_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Int_reduceDvd___redArg(v_e_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object* v_e_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; 
v___x_4547_ = l_Int_reduceDvd___redArg(v_e_4538_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object* v_e_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Int_reduceDvd(v_e_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4578_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4579_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4576_, v___x_4577_, v___x_4578_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26____boxed(lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_();
return v_res_4581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_4585_; uint8_t v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4586_ = 1;
v___x_4587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_);
v___x_4588_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4585_, v___x_4586_, v___x_4587_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28____boxed(lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_();
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_4592_; uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4593_ = 1;
v___x_4594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_);
v___x_4595_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4592_, v___x_4593_, v___x_4594_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30____boxed(lean_object* v_a_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_();
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object* v_inst_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l_Lean_Meta_getNatValue_x3f(v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4663_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4611_ = v___x_4608_;
v_isShared_4612_ = v_isSharedCheck_4663_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4663_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
if (lean_obj_tag(v_a_4609_) == 1)
{
lean_object* v_val_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4658_; 
v_val_4613_ = lean_ctor_get(v_a_4609_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_a_4609_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4615_ = v_a_4609_;
v_isShared_4616_ = v_isSharedCheck_4658_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_val_4613_);
lean_dec(v_a_4609_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4658_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_4601_, v_a_4604_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4649_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4620_ = v___x_4617_;
v_isShared_4621_ = v_isSharedCheck_4649_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4617_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4649_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___y_4623_; lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4630_ = l_Lean_Expr_cleanupAnnotations(v_a_4618_);
v___x_4631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1));
v___x_4632_ = l_Lean_Expr_isConstOf(v___x_4630_, v___x_4631_);
lean_dec_ref(v___x_4630_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4635_; 
lean_del_object(v___x_4620_);
lean_del_object(v___x_4615_);
lean_dec(v_val_4613_);
v___x_4633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4633_);
v___x_4635_ = v___x_4611_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
lean_del_object(v___x_4611_);
v___x_4637_ = lean_nat_to_int(v_val_4613_);
v___x_4638_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4639_ = lean_int_dec_le(v___x_4638_, v___x_4637_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4643_ = lean_int_neg(v___x_4637_);
lean_dec(v___x_4637_);
v___x_4644_ = l_Int_toNat(v___x_4643_);
lean_dec(v___x_4643_);
v___x_4645_ = l_Lean_instToExprInt_mkNat(v___x_4644_);
v___x_4646_ = l_Lean_mkApp3(v___x_4640_, v___x_4641_, v___x_4642_, v___x_4645_);
v___y_4623_ = v___x_4646_;
goto v___jp_4622_;
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = l_Int_toNat(v___x_4637_);
lean_dec(v___x_4637_);
v___x_4648_ = l_Lean_instToExprInt_mkNat(v___x_4647_);
v___y_4623_ = v___x_4648_;
goto v___jp_4622_;
}
}
v___jp_4622_:
{
lean_object* v___x_4625_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set_tag(v___x_4615_, 0);
lean_ctor_set(v___x_4615_, 0, v___y_4623_);
v___x_4625_ = v___x_4615_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___y_4623_);
v___x_4625_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4627_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v___x_4625_);
v___x_4627_ = v___x_4620_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4625_);
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
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_del_object(v___x_4615_);
lean_dec(v_val_4613_);
lean_del_object(v___x_4611_);
v_a_4650_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4617_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4617_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4661_; 
lean_dec(v_a_4609_);
lean_dec_ref(v_inst_4601_);
v___x_4659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4659_);
v___x_4661_ = v___x_4611_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_dec_ref(v_inst_4601_);
v_a_4664_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4608_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4608_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object* v_inst_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec_ref(v_a_4674_);
lean_dec_ref(v_a_4673_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object* v_inst_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4680_, v_a_4681_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object* v_inst_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(v_inst_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object* v_e_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4707_, v_a_4709_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4718_; uint8_t v___x_4719_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v___x_4718_ = l_Lean_Expr_cleanupAnnotations(v_a_4717_);
v___x_4719_ = l_Lean_Expr_isApp(v___x_4718_);
if (v___x_4719_ == 0)
{
lean_dec_ref(v___x_4718_);
goto v___jp_4713_;
}
else
{
lean_object* v_arg_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; 
v_arg_4720_ = lean_ctor_get(v___x_4718_, 1);
lean_inc_ref(v_arg_4720_);
v___x_4721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4718_);
v___x_4722_ = l_Lean_Expr_isApp(v___x_4721_);
if (v___x_4722_ == 0)
{
lean_dec_ref(v___x_4721_);
lean_dec_ref(v_arg_4720_);
goto v___jp_4713_;
}
else
{
lean_object* v_arg_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; 
v_arg_4723_ = lean_ctor_get(v___x_4721_, 1);
lean_inc_ref(v_arg_4723_);
v___x_4724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4721_);
v___x_4725_ = l_Lean_Expr_isApp(v___x_4724_);
if (v___x_4725_ == 0)
{
lean_dec_ref(v___x_4724_);
lean_dec_ref(v_arg_4723_);
lean_dec_ref(v_arg_4720_);
goto v___jp_4713_;
}
else
{
lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4726_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4724_);
v___x_4727_ = ((lean_object*)(l_Int_reduceNatCast___redArg___closed__2));
v___x_4728_ = l_Lean_Expr_isConstOf(v___x_4726_, v___x_4727_);
lean_dec_ref(v___x_4726_);
if (v___x_4728_ == 0)
{
lean_dec_ref(v_arg_4723_);
lean_dec_ref(v_arg_4720_);
goto v___jp_4713_;
}
else
{
lean_object* v___x_4729_; 
v___x_4729_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4723_, v_arg_4720_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
lean_dec_ref(v_arg_4720_);
return v___x_4729_;
}
}
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
v_a_4730_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4716_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4716_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
v___jp_4713_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object* v_e_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Int_reduceNatCast___redArg(v_e_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
lean_dec(v_a_4740_);
lean_dec_ref(v_a_4739_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object* v_e_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = l_Int_reduceNatCast___redArg(v_e_4745_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object* v_e_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l_Int_reduceNatCast(v_e_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_);
lean_dec(v_a_4762_);
lean_dec_ref(v_a_4761_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4784_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4785_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4782_, v___x_4783_, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23____boxed(lean_object* v_a_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_();
return v_res_4787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4791_; uint8_t v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4792_ = 1;
v___x_4793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_);
v___x_4794_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4791_, v___x_4792_, v___x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25____boxed(lean_object* v_a_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_();
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4798_; uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4799_ = 1;
v___x_4800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_);
v___x_4801_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4798_, v___x_4799_, v___x_4800_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27____boxed(lean_object* v_a_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_();
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object* v_e_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4808_, v_a_4810_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
v___x_4819_ = l_Lean_Expr_cleanupAnnotations(v_a_4818_);
v___x_4820_ = l_Lean_Expr_isApp(v___x_4819_);
if (v___x_4820_ == 0)
{
lean_dec_ref(v___x_4819_);
goto v___jp_4814_;
}
else
{
lean_object* v_arg_4821_; lean_object* v___x_4822_; uint8_t v___x_4823_; 
v_arg_4821_ = lean_ctor_get(v___x_4819_, 1);
lean_inc_ref(v_arg_4821_);
v___x_4822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4819_);
v___x_4823_ = l_Lean_Expr_isApp(v___x_4822_);
if (v___x_4823_ == 0)
{
lean_dec_ref(v___x_4822_);
lean_dec_ref(v_arg_4821_);
goto v___jp_4814_;
}
else
{
lean_object* v_arg_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
v_arg_4824_ = lean_ctor_get(v___x_4822_, 1);
lean_inc_ref(v_arg_4824_);
v___x_4825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4822_);
v___x_4826_ = l_Lean_Expr_isApp(v___x_4825_);
if (v___x_4826_ == 0)
{
lean_dec_ref(v___x_4825_);
lean_dec_ref(v_arg_4824_);
lean_dec_ref(v_arg_4821_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v___x_4827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4825_);
v___x_4828_ = ((lean_object*)(l_Int_reduceNatCast_x27___redArg___closed__1));
v___x_4829_ = l_Lean_Expr_isConstOf(v___x_4827_, v___x_4828_);
lean_dec_ref(v___x_4827_);
if (v___x_4829_ == 0)
{
lean_dec_ref(v_arg_4824_);
lean_dec_ref(v_arg_4821_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4830_; 
v___x_4830_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4824_, v_arg_4821_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
lean_dec_ref(v_arg_4821_);
return v___x_4830_;
}
}
}
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_a_4831_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4817_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4817_);
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
v___jp_4814_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object* v_e_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Int_reduceNatCast_x27___redArg(v_e_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object* v_e_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l_Int_reduceNatCast_x27___redArg(v_e_4846_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object* v_e_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Int_reduceNatCast_x27(v_e_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
lean_dec(v_a_4863_);
lean_dec_ref(v_a_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_4872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4873_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4874_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4871_, v___x_4872_, v___x_4873_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23____boxed(lean_object* v_a_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_();
return v_res_4876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4880_; uint8_t v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_4881_ = 1;
v___x_4882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_);
v___x_4883_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4880_, v___x_4881_, v___x_4882_);
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25____boxed(lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_();
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4887_; uint8_t v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_4888_ = 1;
v___x_4889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_);
v___x_4890_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4887_, v___x_4888_, v___x_4889_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27____boxed(lean_object* v_a_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_();
return v_res_4892_;
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
