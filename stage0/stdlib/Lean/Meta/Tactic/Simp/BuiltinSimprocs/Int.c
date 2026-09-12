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
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),LEAN_SCALAR_PTR_LITERAL(43, 197, 90, 191, 152, 17, 164, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_29____boxed(lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_object* v___x_810_; 
lean_inc_ref(v_e_801_);
v___x_810_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_801_, v_a_803_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_869_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_869_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_869_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_869_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = l_Lean_Expr_cleanupAnnotations(v_a_811_);
v___x_816_ = l_Lean_Expr_isApp(v___x_815_);
if (v___x_816_ == 0)
{
lean_dec_ref(v___x_815_);
lean_del_object(v___x_813_);
lean_dec_ref(v_e_801_);
goto v___jp_807_;
}
else
{
lean_object* v_arg_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_arg_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc_ref(v_arg_817_);
v___x_818_ = l_Lean_Expr_appFnCleanup___redArg(v___x_815_);
v___x_819_ = l_Lean_Expr_isApp(v___x_818_);
if (v___x_819_ == 0)
{
lean_dec_ref(v___x_818_);
lean_dec_ref(v_arg_817_);
lean_del_object(v___x_813_);
lean_dec_ref(v_e_801_);
goto v___jp_807_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_818_);
v___x_821_ = l_Lean_Expr_isApp(v___x_820_);
if (v___x_821_ == 0)
{
lean_dec_ref(v___x_820_);
lean_dec_ref(v_arg_817_);
lean_del_object(v___x_813_);
lean_dec_ref(v_e_801_);
goto v___jp_807_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_820_);
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__4));
v___x_824_ = l_Lean_Expr_isConstOf(v___x_822_, v___x_823_);
lean_dec_ref(v___x_822_);
if (v___x_824_ == 0)
{
lean_dec_ref(v_arg_817_);
lean_del_object(v___x_813_);
lean_dec_ref(v_e_801_);
goto v___jp_807_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_826_ = lean_unsigned_to_nat(3u);
v___x_827_ = l_Lean_Expr_isAppOfArity(v_arg_817_, v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec_ref(v_e_801_);
v___x_828_ = l_Lean_Meta_getIntValue_x3f(v_arg_817_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_856_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_856_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_856_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_856_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___y_834_; 
if (lean_obj_tag(v_a_829_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
lean_del_object(v___x_813_);
v_val_839_ = lean_ctor_get(v_a_829_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v_a_829_, 1);
v___x_840_ = lean_int_neg(v_val_839_);
lean_dec(v_val_839_);
v___x_841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_842_ = lean_int_dec_le(v___x_841_, v___x_840_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_846_ = lean_int_neg(v___x_840_);
lean_dec(v___x_840_);
v___x_847_ = l_Int_toNat(v___x_846_);
lean_dec(v___x_846_);
v___x_848_ = l_Lean_instToExprInt_mkNat(v___x_847_);
v___x_849_ = l_Lean_mkApp3(v___x_843_, v___x_844_, v___x_845_, v___x_848_);
v___y_834_ = v___x_849_;
goto v___jp_833_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = l_Int_toNat(v___x_840_);
lean_dec(v___x_840_);
v___x_851_ = l_Lean_instToExprInt_mkNat(v___x_850_);
v___y_834_ = v___x_851_;
goto v___jp_833_;
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_del_object(v___x_831_);
lean_dec(v_a_829_);
v___x_852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_852_);
v___x_854_ = v___x_813_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___y_834_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_835_);
v___x_837_ = v___x_831_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_del_object(v___x_813_);
v_a_857_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_828_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_828_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_867_; 
lean_dec_ref(v_arg_817_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_e_801_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_865_);
v___x_867_ = v___x_813_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
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
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v_e_801_);
v_a_870_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_810_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_810_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
v___jp_807_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___redArg___boxed(lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Int_reduceNeg___redArg(v_e_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Int_reduceNeg___redArg(v_e_885_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNeg___boxed(lean_object* v_e_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Int_reduceNeg(v_e_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_));
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_));
v___x_927_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_928_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_925_, v___x_926_, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25____boxed(lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_();
return v_res_930_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_alloc_closure((void*)(l_Int_reduceNeg___boxed), 9, 0);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_));
v___x_935_ = 1;
v___x_936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_);
v___x_937_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_934_, v___x_935_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27____boxed(lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_();
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_));
v___x_942_ = 1;
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_);
v___x_944_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_941_, v___x_942_, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_29____boxed(lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_29_();
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg(lean_object* v_e_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_953_; 
lean_inc_ref(v_e_947_);
v___x_953_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_947_, v_a_948_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_971_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_971_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_971_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_971_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = l_Lean_Expr_cleanupAnnotations(v_a_954_);
v___x_959_ = l_Lean_Expr_isApp(v___x_958_);
if (v___x_959_ == 0)
{
lean_dec_ref(v___x_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_e_947_);
goto v___jp_950_;
}
else
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_958_);
v___x_961_ = l_Lean_Expr_isApp(v___x_960_);
if (v___x_961_ == 0)
{
lean_dec_ref(v___x_960_);
lean_del_object(v___x_956_);
lean_dec_ref(v_e_947_);
goto v___jp_950_;
}
else
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = l_Lean_Expr_appFnCleanup___redArg(v___x_960_);
v___x_963_ = l_Lean_Expr_isApp(v___x_962_);
if (v___x_963_ == 0)
{
lean_dec_ref(v___x_962_);
lean_del_object(v___x_956_);
lean_dec_ref(v_e_947_);
goto v___jp_950_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_964_ = l_Lean_Expr_appFnCleanup___redArg(v___x_962_);
v___x_965_ = ((lean_object*)(l_Int_reduceNeg___redArg___closed__2));
v___x_966_ = l_Lean_Expr_isConstOf(v___x_964_, v___x_965_);
lean_dec_ref(v___x_964_);
if (v___x_966_ == 0)
{
lean_del_object(v___x_956_);
lean_dec_ref(v_e_947_);
goto v___jp_950_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_e_947_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_967_);
v___x_969_ = v___x_956_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v_e_947_);
v_a_972_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_953_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_953_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___redArg___boxed(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Int_isPosValue___redArg(v_e_980_, v_a_981_);
lean_dec(v_a_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue(lean_object* v_e_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Int_isPosValue___redArg(v_e_984_, v_a_989_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Int_isPosValue___boxed(lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Int_isPosValue(v_e_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1023_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1024_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1021_, v___x_1022_, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23____boxed(lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_();
return v_res_1026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_alloc_closure((void*)(l_Int_isPosValue___boxed), 9, 0);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_isPosValue_declare__32___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_23_));
v___x_1031_ = 1;
v___x_1032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_);
v___x_1033_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1030_, v___x_1031_, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25____boxed(lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_isPosValue___regBuiltin_Int_isPosValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3773715228____hygCtx___hyg_25_();
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg(lean_object* v_e_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = ((lean_object*)(l_Int_reduceAdd___redArg___closed__2));
v___x_1048_ = lean_unsigned_to_nat(6u);
v___x_1049_ = l_Lean_Expr_isAppOfArity(v_e_1041_, v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = l_Lean_Expr_appFn_x21(v_e_1041_);
v___x_1053_ = l_Lean_Expr_appArg_x21(v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_Meta_getIntValue_x3f(v___x_1053_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1108_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1108_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1108_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
if (lean_obj_tag(v_a_1055_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1103_; 
v_val_1059_ = lean_ctor_get(v_a_1055_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_a_1055_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1061_ = v_a_1055_;
v_isShared_1062_ = v_isSharedCheck_1103_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v_a_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1103_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = l_Lean_Expr_appArg_x21(v_e_1041_);
v___x_1064_ = l_Lean_Meta_getIntValue_x3f(v___x_1063_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1094_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1094_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1094_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___y_1070_; 
if (lean_obj_tag(v_a_1065_) == 1)
{
lean_object* v_val_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
lean_del_object(v___x_1057_);
v_val_1077_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_val_1077_);
lean_dec_ref_known(v_a_1065_, 1);
v___x_1078_ = lean_int_add(v_val_1059_, v_val_1077_);
lean_dec(v_val_1077_);
lean_dec(v_val_1059_);
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1080_ = lean_int_dec_le(v___x_1079_, v___x_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1083_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1084_ = lean_int_neg(v___x_1078_);
lean_dec(v___x_1078_);
v___x_1085_ = l_Int_toNat(v___x_1084_);
lean_dec(v___x_1084_);
v___x_1086_ = l_Lean_instToExprInt_mkNat(v___x_1085_);
v___x_1087_ = l_Lean_mkApp3(v___x_1081_, v___x_1082_, v___x_1083_, v___x_1086_);
v___y_1070_ = v___x_1087_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = l_Int_toNat(v___x_1078_);
lean_dec(v___x_1078_);
v___x_1089_ = l_Lean_instToExprInt_mkNat(v___x_1088_);
v___y_1070_ = v___x_1089_;
goto v___jp_1069_;
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_del_object(v___x_1067_);
lean_dec(v_a_1065_);
lean_del_object(v___x_1061_);
lean_dec(v_val_1059_);
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1090_);
v___x_1092_ = v___x_1057_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
v___jp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1070_);
v___x_1072_ = v___x_1061_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___y_1070_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1072_);
v___x_1074_ = v___x_1067_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_1061_);
lean_dec(v_val_1059_);
lean_del_object(v___x_1057_);
v_a_1095_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1064_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1064_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v_a_1055_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1104_);
v___x_1106_ = v___x_1057_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
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
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1054_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1054_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___redArg___boxed(lean_object* v_e_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Int_reduceAdd___redArg(v_e_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_e_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd(lean_object* v_e_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Int_reduceAdd___redArg(v_e_1124_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAdd___boxed(lean_object* v_e_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Int_reduceAdd(v_e_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_e_1134_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1166_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1167_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1164_, v___x_1165_, v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26____boxed(lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_();
return v_res_1169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_alloc_closure((void*)(l_Int_reduceAdd___boxed), 9, 0);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1174_ = 1;
v___x_1175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_);
v___x_1176_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1173_, v___x_1174_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28____boxed(lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_();
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAdd_declare__37___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_26_));
v___x_1181_ = 1;
v___x_1182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_28_);
v___x_1183_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1180_, v___x_1181_, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30____boxed(lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAdd___regBuiltin_Int_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_82623176____hygCtx___hyg_30_();
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg(lean_object* v_e_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = ((lean_object*)(l_Int_reduceMul___redArg___closed__2));
v___x_1198_ = lean_unsigned_to_nat(6u);
v___x_1199_ = l_Lean_Expr_isAppOfArity(v_e_1191_, v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = l_Lean_Expr_appFn_x21(v_e_1191_);
v___x_1203_ = l_Lean_Expr_appArg_x21(v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = l_Lean_Meta_getIntValue_x3f(v___x_1203_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1258_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1258_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1258_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
if (lean_obj_tag(v_a_1205_) == 1)
{
lean_object* v_val_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1253_; 
v_val_1209_ = lean_ctor_get(v_a_1205_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_a_1205_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1211_ = v_a_1205_;
v_isShared_1212_ = v_isSharedCheck_1253_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_val_1209_);
lean_dec(v_a_1205_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1253_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = l_Lean_Expr_appArg_x21(v_e_1191_);
v___x_1214_ = l_Lean_Meta_getIntValue_x3f(v___x_1213_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1244_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1244_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1244_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___y_1220_; 
if (lean_obj_tag(v_a_1215_) == 1)
{
lean_object* v_val_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
lean_del_object(v___x_1207_);
v_val_1227_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_a_1215_, 1);
v___x_1228_ = lean_int_mul(v_val_1209_, v_val_1227_);
lean_dec(v_val_1227_);
lean_dec(v_val_1209_);
v___x_1229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1230_ = lean_int_dec_le(v___x_1229_, v___x_1228_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1234_ = lean_int_neg(v___x_1228_);
lean_dec(v___x_1228_);
v___x_1235_ = l_Int_toNat(v___x_1234_);
lean_dec(v___x_1234_);
v___x_1236_ = l_Lean_instToExprInt_mkNat(v___x_1235_);
v___x_1237_ = l_Lean_mkApp3(v___x_1231_, v___x_1232_, v___x_1233_, v___x_1236_);
v___y_1220_ = v___x_1237_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = l_Int_toNat(v___x_1228_);
lean_dec(v___x_1228_);
v___x_1239_ = l_Lean_instToExprInt_mkNat(v___x_1238_);
v___y_1220_ = v___x_1239_;
goto v___jp_1219_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_del_object(v___x_1217_);
lean_dec(v_a_1215_);
lean_del_object(v___x_1211_);
lean_dec(v_val_1209_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1240_);
v___x_1242_ = v___x_1207_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
v___jp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 0);
lean_ctor_set(v___x_1211_, 0, v___y_1220_);
v___x_1222_ = v___x_1211_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___y_1220_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1222_);
v___x_1224_ = v___x_1217_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_del_object(v___x_1211_);
lean_dec(v_val_1209_);
lean_del_object(v___x_1207_);
v_a_1245_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1214_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1214_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_dec(v_a_1205_);
v___x_1254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1254_);
v___x_1256_ = v___x_1207_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1204_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1204_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___redArg___boxed(lean_object* v_e_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Int_reduceMul___redArg(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec_ref(v_e_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul(lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Int_reduceMul___redArg(v_e_1274_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMul___boxed(lean_object* v_e_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Int_reduceMul(v_e_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_e_1284_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1316_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1317_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1314_, v___x_1315_, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26____boxed(lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_();
return v_res_1319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_alloc_closure((void*)(l_Int_reduceMul___boxed), 9, 0);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1324_ = 1;
v___x_1325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_);
v___x_1326_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1323_, v___x_1324_, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28____boxed(lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_();
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMul_declare__42___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_26_));
v___x_1331_ = 1;
v___x_1332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_28_);
v___x_1333_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1330_, v___x_1331_, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30____boxed(lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMul___regBuiltin_Int_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2821223409____hygCtx___hyg_30_();
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg(lean_object* v_e_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1347_ = ((lean_object*)(l_Int_reduceSub___redArg___closed__2));
v___x_1348_ = lean_unsigned_to_nat(6u);
v___x_1349_ = l_Lean_Expr_isAppOfArity(v_e_1341_, v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = l_Lean_Expr_appFn_x21(v_e_1341_);
v___x_1353_ = l_Lean_Expr_appArg_x21(v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = l_Lean_Meta_getIntValue_x3f(v___x_1353_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1408_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1408_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1408_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
if (lean_obj_tag(v_a_1355_) == 1)
{
lean_object* v_val_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1403_; 
v_val_1359_ = lean_ctor_get(v_a_1355_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_a_1355_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1361_ = v_a_1355_;
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_val_1359_);
lean_dec(v_a_1355_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = l_Lean_Expr_appArg_x21(v_e_1341_);
v___x_1364_ = l_Lean_Meta_getIntValue_x3f(v___x_1363_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1394_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1394_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1394_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___y_1370_; 
if (lean_obj_tag(v_a_1365_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
lean_del_object(v___x_1357_);
v_val_1377_ = lean_ctor_get(v_a_1365_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v_a_1365_, 1);
v___x_1378_ = lean_int_sub(v_val_1359_, v_val_1377_);
lean_dec(v_val_1377_);
lean_dec(v_val_1359_);
v___x_1379_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1380_ = lean_int_dec_le(v___x_1379_, v___x_1378_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1384_ = lean_int_neg(v___x_1378_);
lean_dec(v___x_1378_);
v___x_1385_ = l_Int_toNat(v___x_1384_);
lean_dec(v___x_1384_);
v___x_1386_ = l_Lean_instToExprInt_mkNat(v___x_1385_);
v___x_1387_ = l_Lean_mkApp3(v___x_1381_, v___x_1382_, v___x_1383_, v___x_1386_);
v___y_1370_ = v___x_1387_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = l_Int_toNat(v___x_1378_);
lean_dec(v___x_1378_);
v___x_1389_ = l_Lean_instToExprInt_mkNat(v___x_1388_);
v___y_1370_ = v___x_1389_;
goto v___jp_1369_;
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_del_object(v___x_1367_);
lean_dec(v_a_1365_);
lean_del_object(v___x_1361_);
lean_dec(v_val_1359_);
v___x_1390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1390_);
v___x_1392_ = v___x_1357_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
v___jp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1370_);
v___x_1372_ = v___x_1361_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___y_1370_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1372_);
v___x_1374_ = v___x_1367_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1361_);
lean_dec(v_val_1359_);
lean_del_object(v___x_1357_);
v_a_1395_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1364_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1364_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_dec(v_a_1355_);
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1404_);
v___x_1406_ = v___x_1357_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1354_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1354_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___redArg___boxed(lean_object* v_e_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Int_reduceSub___redArg(v_e_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec_ref(v_e_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub(lean_object* v_e_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Int_reduceSub___redArg(v_e_1424_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceSub___boxed(lean_object* v_e_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Int_reduceSub(v_e_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_e_1434_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1466_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1467_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1464_, v___x_1465_, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26____boxed(lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_();
return v_res_1469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_alloc_closure((void*)(l_Int_reduceSub___boxed), 9, 0);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1474_ = 1;
v___x_1475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_);
v___x_1476_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1473_, v___x_1474_, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28____boxed(lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_();
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceSub_declare__47___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_26_));
v___x_1481_ = 1;
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_28_);
v___x_1483_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1480_, v___x_1481_, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30____boxed(lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceSub___regBuiltin_Int_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548404080____hygCtx___hyg_30_();
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg(lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = ((lean_object*)(l_Int_reduceDiv___redArg___closed__2));
v___x_1498_ = lean_unsigned_to_nat(6u);
v___x_1499_ = l_Lean_Expr_isAppOfArity(v_e_1491_, v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = l_Lean_Expr_appFn_x21(v_e_1491_);
v___x_1503_ = l_Lean_Expr_appArg_x21(v___x_1502_);
lean_dec_ref(v___x_1502_);
v___x_1504_ = l_Lean_Meta_getIntValue_x3f(v___x_1503_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1558_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1558_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1558_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
if (lean_obj_tag(v_a_1505_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1553_; 
v_val_1509_ = lean_ctor_get(v_a_1505_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_a_1505_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1511_ = v_a_1505_;
v_isShared_1512_ = v_isSharedCheck_1553_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_val_1509_);
lean_dec(v_a_1505_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1553_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = l_Lean_Expr_appArg_x21(v_e_1491_);
v___x_1514_ = l_Lean_Meta_getIntValue_x3f(v___x_1513_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1544_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1544_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1544_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___y_1520_; 
if (lean_obj_tag(v_a_1515_) == 1)
{
lean_object* v_val_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
lean_del_object(v___x_1507_);
v_val_1527_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v_a_1515_, 1);
v___x_1528_ = lean_int_ediv(v_val_1509_, v_val_1527_);
lean_dec(v_val_1527_);
lean_dec(v_val_1509_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1530_ = lean_int_dec_le(v___x_1529_, v___x_1528_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1534_ = lean_int_neg(v___x_1528_);
lean_dec(v___x_1528_);
v___x_1535_ = l_Int_toNat(v___x_1534_);
lean_dec(v___x_1534_);
v___x_1536_ = l_Lean_instToExprInt_mkNat(v___x_1535_);
v___x_1537_ = l_Lean_mkApp3(v___x_1531_, v___x_1532_, v___x_1533_, v___x_1536_);
v___y_1520_ = v___x_1537_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = l_Int_toNat(v___x_1528_);
lean_dec(v___x_1528_);
v___x_1539_ = l_Lean_instToExprInt_mkNat(v___x_1538_);
v___y_1520_ = v___x_1539_;
goto v___jp_1519_;
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_del_object(v___x_1517_);
lean_dec(v_a_1515_);
lean_del_object(v___x_1511_);
lean_dec(v_val_1509_);
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1540_);
v___x_1542_ = v___x_1507_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
v___jp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 0);
lean_ctor_set(v___x_1511_, 0, v___y_1520_);
v___x_1522_ = v___x_1511_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___y_1520_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1522_);
v___x_1524_ = v___x_1517_;
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
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_del_object(v___x_1511_);
lean_dec(v_val_1509_);
lean_del_object(v___x_1507_);
v_a_1545_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1514_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1514_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_dec(v_a_1505_);
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1554_);
v___x_1556_ = v___x_1507_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1504_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1504_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___redArg___boxed(lean_object* v_e_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Int_reduceDiv___redArg(v_e_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec_ref(v_e_1567_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv(lean_object* v_e_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Int_reduceDiv___redArg(v_e_1574_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDiv___boxed(lean_object* v_e_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Int_reduceDiv(v_e_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_e_1584_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1616_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1617_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1614_, v___x_1615_, v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26____boxed(lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_();
return v_res_1619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_alloc_closure((void*)(l_Int_reduceDiv___boxed), 9, 0);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1624_ = 1;
v___x_1625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_);
v___x_1626_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1623_, v___x_1624_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28____boxed(lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_();
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDiv_declare__52___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_26_));
v___x_1631_ = 1;
v___x_1632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_28_);
v___x_1633_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1630_, v___x_1631_, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30____boxed(lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDiv___regBuiltin_Int_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4225399930____hygCtx___hyg_30_();
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg(lean_object* v_e_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = ((lean_object*)(l_Int_reduceMod___redArg___closed__2));
v___x_1648_ = lean_unsigned_to_nat(6u);
v___x_1649_ = l_Lean_Expr_isAppOfArity(v_e_1641_, v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = l_Lean_Expr_appFn_x21(v_e_1641_);
v___x_1653_ = l_Lean_Expr_appArg_x21(v___x_1652_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = l_Lean_Meta_getIntValue_x3f(v___x_1653_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1708_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1708_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1708_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
if (lean_obj_tag(v_a_1655_) == 1)
{
lean_object* v_val_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1703_; 
v_val_1659_ = lean_ctor_get(v_a_1655_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_a_1655_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1661_ = v_a_1655_;
v_isShared_1662_ = v_isSharedCheck_1703_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_val_1659_);
lean_dec(v_a_1655_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1703_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = l_Lean_Expr_appArg_x21(v_e_1641_);
v___x_1664_ = l_Lean_Meta_getIntValue_x3f(v___x_1663_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1694_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1694_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1694_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___y_1670_; 
if (lean_obj_tag(v_a_1665_) == 1)
{
lean_object* v_val_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
lean_del_object(v___x_1657_);
v_val_1677_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v_a_1665_, 1);
v___x_1678_ = lean_int_emod(v_val_1659_, v_val_1677_);
lean_dec(v_val_1677_);
lean_dec(v_val_1659_);
v___x_1679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1680_ = lean_int_dec_le(v___x_1679_, v___x_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1684_ = lean_int_neg(v___x_1678_);
lean_dec(v___x_1678_);
v___x_1685_ = l_Int_toNat(v___x_1684_);
lean_dec(v___x_1684_);
v___x_1686_ = l_Lean_instToExprInt_mkNat(v___x_1685_);
v___x_1687_ = l_Lean_mkApp3(v___x_1681_, v___x_1682_, v___x_1683_, v___x_1686_);
v___y_1670_ = v___x_1687_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = l_Int_toNat(v___x_1678_);
lean_dec(v___x_1678_);
v___x_1689_ = l_Lean_instToExprInt_mkNat(v___x_1688_);
v___y_1670_ = v___x_1689_;
goto v___jp_1669_;
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
lean_del_object(v___x_1667_);
lean_dec(v_a_1665_);
lean_del_object(v___x_1661_);
lean_dec(v_val_1659_);
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1690_);
v___x_1692_ = v___x_1657_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
v___jp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1670_);
v___x_1672_ = v___x_1661_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___y_1670_);
v___x_1672_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1672_);
v___x_1674_ = v___x_1667_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_del_object(v___x_1661_);
lean_dec(v_val_1659_);
lean_del_object(v___x_1657_);
v_a_1695_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1664_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1664_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_dec(v_a_1655_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1704_);
v___x_1706_ = v___x_1657_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_a_1709_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1654_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1654_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___redArg___boxed(lean_object* v_e_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Int_reduceMod___redArg(v_e_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec_ref(v_e_1717_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod(lean_object* v_e_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Int_reduceMod___redArg(v_e_1724_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceMod___boxed(lean_object* v_e_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Int_reduceMod(v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_e_1734_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1766_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1767_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1764_, v___x_1765_, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26____boxed(lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_();
return v_res_1769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_alloc_closure((void*)(l_Int_reduceMod___boxed), 9, 0);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1774_ = 1;
v___x_1775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_);
v___x_1776_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1773_, v___x_1774_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28____boxed(lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_();
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceMod_declare__57___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_26_));
v___x_1781_ = 1;
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_28_);
v___x_1783_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1780_, v___x_1781_, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30____boxed(lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceMod___regBuiltin_Int_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2833796642____hygCtx___hyg_30_();
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg(lean_object* v_e_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = ((lean_object*)(l_Int_reduceTDiv___redArg___closed__1));
v___x_1797_ = lean_unsigned_to_nat(2u);
v___x_1798_ = l_Lean_Expr_isAppOfArity(v_e_1790_, v___x_1796_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = l_Lean_Expr_appFn_x21(v_e_1790_);
v___x_1802_ = l_Lean_Expr_appArg_x21(v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = l_Lean_Meta_getIntValue_x3f(v___x_1802_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1857_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1857_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1857_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
if (lean_obj_tag(v_a_1804_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1852_; 
v_val_1808_ = lean_ctor_get(v_a_1804_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_a_1804_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1810_ = v_a_1804_;
v_isShared_1811_ = v_isSharedCheck_1852_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_val_1808_);
lean_dec(v_a_1804_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1852_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = l_Lean_Expr_appArg_x21(v_e_1790_);
v___x_1813_ = l_Lean_Meta_getIntValue_x3f(v___x_1812_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1843_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1843_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1843_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___y_1819_; 
if (lean_obj_tag(v_a_1814_) == 1)
{
lean_object* v_val_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
lean_del_object(v___x_1806_);
v_val_1826_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v_a_1814_, 1);
v___x_1827_ = lean_int_div(v_val_1808_, v_val_1826_);
lean_dec(v_val_1826_);
lean_dec(v_val_1808_);
v___x_1828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1829_ = lean_int_dec_le(v___x_1828_, v___x_1827_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1833_ = lean_int_neg(v___x_1827_);
lean_dec(v___x_1827_);
v___x_1834_ = l_Int_toNat(v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = l_Lean_instToExprInt_mkNat(v___x_1834_);
v___x_1836_ = l_Lean_mkApp3(v___x_1830_, v___x_1831_, v___x_1832_, v___x_1835_);
v___y_1819_ = v___x_1836_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = l_Int_toNat(v___x_1827_);
lean_dec(v___x_1827_);
v___x_1838_ = l_Lean_instToExprInt_mkNat(v___x_1837_);
v___y_1819_ = v___x_1838_;
goto v___jp_1818_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_del_object(v___x_1816_);
lean_dec(v_a_1814_);
lean_del_object(v___x_1810_);
lean_dec(v_val_1808_);
v___x_1839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1839_);
v___x_1841_ = v___x_1806_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
v___jp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 0);
lean_ctor_set(v___x_1810_, 0, v___y_1819_);
v___x_1821_ = v___x_1810_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___y_1819_);
v___x_1821_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1821_);
v___x_1823_ = v___x_1816_;
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
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_del_object(v___x_1810_);
lean_dec(v_val_1808_);
lean_del_object(v___x_1806_);
v_a_1844_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1813_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1813_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec(v_a_1804_);
v___x_1853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1853_);
v___x_1855_ = v___x_1806_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
v_a_1858_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1803_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1803_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___redArg___boxed(lean_object* v_e_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Int_reduceTDiv___redArg(v_e_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec_ref(v_e_1866_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv(lean_object* v_e_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Int_reduceTDiv___redArg(v_e_1873_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTDiv___boxed(lean_object* v_e_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Int_reduceTDiv(v_e_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_e_1883_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1910_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1911_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1908_, v___x_1909_, v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21____boxed(lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_();
return v_res_1913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_alloc_closure((void*)(l_Int_reduceTDiv___boxed), 9, 0);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1918_ = 1;
v___x_1919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_);
v___x_1920_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1917_, v___x_1918_, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23____boxed(lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_();
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTDiv_declare__62___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_21_));
v___x_1925_ = 1;
v___x_1926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_23_);
v___x_1927_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1924_, v___x_1925_, v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25____boxed(lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTDiv___regBuiltin_Int_reduceTDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_909854703____hygCtx___hyg_25_();
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg(lean_object* v_e_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = ((lean_object*)(l_Int_reduceTMod___redArg___closed__1));
v___x_1941_ = lean_unsigned_to_nat(2u);
v___x_1942_ = l_Lean_Expr_isAppOfArity(v_e_1934_, v___x_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = l_Lean_Expr_appFn_x21(v_e_1934_);
v___x_1946_ = l_Lean_Expr_appArg_x21(v___x_1945_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = l_Lean_Meta_getIntValue_x3f(v___x_1946_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2001_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_2001_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2001_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
if (lean_obj_tag(v_a_1948_) == 1)
{
lean_object* v_val_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1996_; 
v_val_1952_ = lean_ctor_get(v_a_1948_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1954_ = v_a_1948_;
v_isShared_1955_ = v_isSharedCheck_1996_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_val_1952_);
lean_dec(v_a_1948_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1996_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = l_Lean_Expr_appArg_x21(v_e_1934_);
v___x_1957_ = l_Lean_Meta_getIntValue_x3f(v___x_1956_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1987_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1987_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1987_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___y_1963_; 
if (lean_obj_tag(v_a_1958_) == 1)
{
lean_object* v_val_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
lean_del_object(v___x_1950_);
v_val_1970_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_a_1958_, 1);
v___x_1971_ = lean_int_mod(v_val_1952_, v_val_1970_);
lean_dec(v_val_1970_);
lean_dec(v_val_1952_);
v___x_1972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_1973_ = lean_int_dec_le(v___x_1972_, v___x_1971_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_1975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_1976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_1977_ = lean_int_neg(v___x_1971_);
lean_dec(v___x_1971_);
v___x_1978_ = l_Int_toNat(v___x_1977_);
lean_dec(v___x_1977_);
v___x_1979_ = l_Lean_instToExprInt_mkNat(v___x_1978_);
v___x_1980_ = l_Lean_mkApp3(v___x_1974_, v___x_1975_, v___x_1976_, v___x_1979_);
v___y_1963_ = v___x_1980_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = l_Int_toNat(v___x_1971_);
lean_dec(v___x_1971_);
v___x_1982_ = l_Lean_instToExprInt_mkNat(v___x_1981_);
v___y_1963_ = v___x_1982_;
goto v___jp_1962_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_del_object(v___x_1960_);
lean_dec(v_a_1958_);
lean_del_object(v___x_1954_);
lean_dec(v_val_1952_);
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1983_);
v___x_1985_ = v___x_1950_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
v___jp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 0);
lean_ctor_set(v___x_1954_, 0, v___y_1963_);
v___x_1965_ = v___x_1954_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___y_1963_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1965_);
v___x_1967_ = v___x_1960_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_del_object(v___x_1954_);
lean_dec(v_val_1952_);
lean_del_object(v___x_1950_);
v_a_1988_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1957_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1957_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_dec(v_a_1948_);
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1997_);
v___x_1999_ = v___x_1950_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
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
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1947_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1947_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___redArg___boxed(lean_object* v_e_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Int_reduceTMod___redArg(v_e_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_e_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod(lean_object* v_e_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Int_reduceTMod___redArg(v_e_2017_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceTMod___boxed(lean_object* v_e_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Int_reduceTMod(v_e_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_e_2027_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2054_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2055_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2052_, v___x_2053_, v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21____boxed(lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_();
return v_res_2057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_alloc_closure((void*)(l_Int_reduceTMod___boxed), 9, 0);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2062_ = 1;
v___x_2063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_);
v___x_2064_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2061_, v___x_2062_, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23____boxed(lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_();
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceTMod_declare__67___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_21_));
v___x_2069_ = 1;
v___x_2070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_23_);
v___x_2071_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2068_, v___x_2069_, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25____boxed(lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceTMod___regBuiltin_Int_reduceTMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2219245926____hygCtx___hyg_25_();
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg(lean_object* v_e_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2084_ = ((lean_object*)(l_Int_reduceFDiv___redArg___closed__1));
v___x_2085_ = lean_unsigned_to_nat(2u);
v___x_2086_ = l_Lean_Expr_isAppOfArity(v_e_2078_, v___x_2084_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = l_Lean_Expr_appFn_x21(v_e_2078_);
v___x_2090_ = l_Lean_Expr_appArg_x21(v___x_2089_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = l_Lean_Meta_getIntValue_x3f(v___x_2090_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2145_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2145_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2145_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
if (lean_obj_tag(v_a_2092_) == 1)
{
lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2140_; 
v_val_2096_ = lean_ctor_get(v_a_2092_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2098_ = v_a_2092_;
v_isShared_2099_ = v_isSharedCheck_2140_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_dec(v_a_2092_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2140_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = l_Lean_Expr_appArg_x21(v_e_2078_);
v___x_2101_ = l_Lean_Meta_getIntValue_x3f(v___x_2100_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2131_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2131_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2131_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___y_2107_; 
if (lean_obj_tag(v_a_2102_) == 1)
{
lean_object* v_val_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
lean_del_object(v___x_2094_);
v_val_2114_ = lean_ctor_get(v_a_2102_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v_a_2102_, 1);
v___x_2115_ = l_Int_fdiv(v_val_2096_, v_val_2114_);
lean_dec(v_val_2114_);
lean_dec(v_val_2096_);
v___x_2116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2117_ = lean_int_dec_le(v___x_2116_, v___x_2115_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2121_ = lean_int_neg(v___x_2115_);
lean_dec(v___x_2115_);
v___x_2122_ = l_Int_toNat(v___x_2121_);
lean_dec(v___x_2121_);
v___x_2123_ = l_Lean_instToExprInt_mkNat(v___x_2122_);
v___x_2124_ = l_Lean_mkApp3(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2123_);
v___y_2107_ = v___x_2124_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = l_Int_toNat(v___x_2115_);
lean_dec(v___x_2115_);
v___x_2126_ = l_Lean_instToExprInt_mkNat(v___x_2125_);
v___y_2107_ = v___x_2126_;
goto v___jp_2106_;
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_del_object(v___x_2104_);
lean_dec(v_a_2102_);
lean_del_object(v___x_2098_);
lean_dec(v_val_2096_);
v___x_2127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2127_);
v___x_2129_ = v___x_2094_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
v___jp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 0);
lean_ctor_set(v___x_2098_, 0, v___y_2107_);
v___x_2109_ = v___x_2098_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___y_2107_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2109_);
v___x_2111_ = v___x_2104_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2098_);
lean_dec(v_val_2096_);
lean_del_object(v___x_2094_);
v_a_2132_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2101_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2101_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec(v_a_2092_);
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2141_);
v___x_2143_ = v___x_2094_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_a_2146_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2091_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2091_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___redArg___boxed(lean_object* v_e_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Int_reduceFDiv___redArg(v_e_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_e_2154_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv(lean_object* v_e_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Int_reduceFDiv___redArg(v_e_2161_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFDiv___boxed(lean_object* v_e_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Int_reduceFDiv(v_e_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_e_2171_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2198_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2199_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2196_, v___x_2197_, v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21____boxed(lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_();
return v_res_2201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_alloc_closure((void*)(l_Int_reduceFDiv___boxed), 9, 0);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2206_ = 1;
v___x_2207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_);
v___x_2208_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2205_, v___x_2206_, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23____boxed(lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_();
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFDiv_declare__72___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_21_));
v___x_2213_ = 1;
v___x_2214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_23_);
v___x_2215_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2212_, v___x_2213_, v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25____boxed(lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFDiv___regBuiltin_Int_reduceFDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3466108805____hygCtx___hyg_25_();
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2228_ = ((lean_object*)(l_Int_reduceFMod___redArg___closed__1));
v___x_2229_ = lean_unsigned_to_nat(2u);
v___x_2230_ = l_Lean_Expr_isAppOfArity(v_e_2222_, v___x_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = l_Lean_Expr_appFn_x21(v_e_2222_);
v___x_2234_ = l_Lean_Expr_appArg_x21(v___x_2233_);
lean_dec_ref(v___x_2233_);
v___x_2235_ = l_Lean_Meta_getIntValue_x3f(v___x_2234_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2289_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2289_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2289_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_val_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2284_; 
v_val_2240_ = lean_ctor_get(v_a_2236_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_a_2236_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2242_ = v_a_2236_;
v_isShared_2243_ = v_isSharedCheck_2284_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_val_2240_);
lean_dec(v_a_2236_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2284_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = l_Lean_Expr_appArg_x21(v_e_2222_);
v___x_2245_ = l_Lean_Meta_getIntValue_x3f(v___x_2244_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2275_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2275_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2275_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___y_2251_; 
if (lean_obj_tag(v_a_2246_) == 1)
{
lean_object* v_val_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
lean_del_object(v___x_2238_);
v_val_2258_ = lean_ctor_get(v_a_2246_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v_a_2246_, 1);
v___x_2259_ = l_Int_fmod(v_val_2240_, v_val_2258_);
lean_dec(v_val_2258_);
lean_dec(v_val_2240_);
v___x_2260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2261_ = lean_int_dec_le(v___x_2260_, v___x_2259_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2265_ = lean_int_neg(v___x_2259_);
lean_dec(v___x_2259_);
v___x_2266_ = l_Int_toNat(v___x_2265_);
lean_dec(v___x_2265_);
v___x_2267_ = l_Lean_instToExprInt_mkNat(v___x_2266_);
v___x_2268_ = l_Lean_mkApp3(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2267_);
v___y_2251_ = v___x_2268_;
goto v___jp_2250_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = l_Int_toNat(v___x_2259_);
lean_dec(v___x_2259_);
v___x_2270_ = l_Lean_instToExprInt_mkNat(v___x_2269_);
v___y_2251_ = v___x_2270_;
goto v___jp_2250_;
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
lean_del_object(v___x_2248_);
lean_dec(v_a_2246_);
lean_del_object(v___x_2242_);
lean_dec(v_val_2240_);
v___x_2271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2271_);
v___x_2273_ = v___x_2238_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
v___jp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 0);
lean_ctor_set(v___x_2242_, 0, v___y_2251_);
v___x_2253_ = v___x_2242_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___y_2251_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2253_);
v___x_2255_ = v___x_2248_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2242_);
lean_dec(v_val_2240_);
lean_del_object(v___x_2238_);
v_a_2276_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2245_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2245_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec(v_a_2236_);
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2285_);
v___x_2287_ = v___x_2238_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2235_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2235_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___redArg___boxed(lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Int_reduceFMod___redArg(v_e_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v_e_2298_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod(lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Int_reduceFMod___redArg(v_e_2305_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceFMod___boxed(lean_object* v_e_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Int_reduceFMod(v_e_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_e_2315_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2342_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2343_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2340_, v___x_2341_, v___x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21____boxed(lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_();
return v_res_2345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_alloc_closure((void*)(l_Int_reduceFMod___boxed), 9, 0);
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2350_ = 1;
v___x_2351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_);
v___x_2352_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2349_, v___x_2350_, v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23____boxed(lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_();
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceFMod_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_21_));
v___x_2357_ = 1;
v___x_2358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_23_);
v___x_2359_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2356_, v___x_2357_, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25____boxed(lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceFMod___regBuiltin_Int_reduceFMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2758920464____hygCtx___hyg_25_();
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg(lean_object* v_e_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__1));
v___x_2374_ = ((lean_object*)(l_Int_reduceBdiv___redArg___closed__2));
v___x_2375_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v___x_2373_, v___x_2374_, v_e_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___redArg___boxed(lean_object* v_e_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Int_reduceBdiv___redArg(v_e_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec_ref(v_e_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv(lean_object* v_e_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Int_reduceBdiv___redArg(v_e_2383_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBdiv___boxed(lean_object* v_e_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Int_reduceBdiv(v_e_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_e_2393_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2420_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2421_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2418_, v___x_2419_, v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21____boxed(lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_();
return v_res_2423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_alloc_closure((void*)(l_Int_reduceBdiv___boxed), 9, 0);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2428_ = 1;
v___x_2429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_);
v___x_2430_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2427_, v___x_2428_, v___x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23____boxed(lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_();
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBdiv_declare__82___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_21_));
v___x_2435_ = 1;
v___x_2436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_23_);
v___x_2437_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2434_, v___x_2435_, v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25____boxed(lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBdiv___regBuiltin_Int_reduceBdiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1168855926____hygCtx___hyg_25_();
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg(lean_object* v_e_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__1));
v___x_2452_ = ((lean_object*)(l_Int_reduceBmod___redArg___closed__2));
v___x_2453_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinIntNatOp___redArg(v___x_2451_, v___x_2452_, v_e_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___redArg___boxed(lean_object* v_e_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Int_reduceBmod___redArg(v_e_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec_ref(v_e_2454_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod(lean_object* v_e_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Int_reduceBmod___redArg(v_e_2461_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBmod___boxed(lean_object* v_e_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Int_reduceBmod(v_e_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_e_2471_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2498_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2499_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2496_, v___x_2497_, v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21____boxed(lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_();
return v_res_2501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_alloc_closure((void*)(l_Int_reduceBmod___boxed), 9, 0);
v___x_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2506_ = 1;
v___x_2507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_);
v___x_2508_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2505_, v___x_2506_, v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23____boxed(lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_();
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBmod_declare__87___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_21_));
v___x_2513_ = 1;
v___x_2514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_23_);
v___x_2515_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2512_, v___x_2513_, v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25____boxed(lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBmod___regBuiltin_Int_reduceBmod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_618080867____hygCtx___hyg_25_();
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg(lean_object* v_e_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2523_, v_a_2526_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = l_Lean_Expr_cleanupAnnotations(v_a_2534_);
v___x_2536_ = l_Lean_Expr_isApp(v___x_2535_);
if (v___x_2536_ == 0)
{
lean_dec_ref(v___x_2535_);
goto v___jp_2530_;
}
else
{
lean_object* v_arg_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_arg_2537_ = lean_ctor_get(v___x_2535_, 1);
lean_inc_ref(v_arg_2537_);
v___x_2538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2535_);
v___x_2539_ = l_Lean_Expr_isApp(v___x_2538_);
if (v___x_2539_ == 0)
{
lean_dec_ref(v___x_2538_);
lean_dec_ref(v_arg_2537_);
goto v___jp_2530_;
}
else
{
lean_object* v_arg_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_arg_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc_ref(v_arg_2540_);
v___x_2541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2538_);
v___x_2542_ = l_Lean_Expr_isApp(v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v___x_2541_);
lean_dec_ref(v_arg_2540_);
lean_dec_ref(v_arg_2537_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2541_);
v___x_2544_ = l_Lean_Expr_isApp(v___x_2543_);
if (v___x_2544_ == 0)
{
lean_dec_ref(v___x_2543_);
lean_dec_ref(v_arg_2540_);
lean_dec_ref(v_arg_2537_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2545_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2543_);
v___x_2546_ = l_Lean_Expr_isApp(v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec_ref(v___x_2545_);
lean_dec_ref(v_arg_2540_);
lean_dec_ref(v_arg_2537_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2547_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2545_);
v___x_2548_ = l_Lean_Expr_isApp(v___x_2547_);
if (v___x_2548_ == 0)
{
lean_dec_ref(v___x_2547_);
lean_dec_ref(v_arg_2540_);
lean_dec_ref(v_arg_2537_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2549_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2547_);
v___x_2550_ = ((lean_object*)(l_Int_reducePow___redArg___closed__2));
v___x_2551_ = l_Lean_Expr_isConstOf(v___x_2549_, v___x_2550_);
lean_dec_ref(v___x_2549_);
if (v___x_2551_ == 0)
{
lean_dec_ref(v_arg_2540_);
lean_dec_ref(v_arg_2537_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Meta_getIntValue_x3f(v_arg_2540_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2626_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2626_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2626_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
if (lean_obj_tag(v_a_2553_) == 1)
{
lean_object* v_val_2557_; lean_object* v___x_2558_; 
lean_del_object(v___x_2555_);
v_val_2557_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_val_2557_);
lean_dec_ref_known(v_a_2553_, 1);
v___x_2558_ = l_Lean_Meta_getNatValue_x3f(v_arg_2537_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec_ref(v_arg_2537_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2613_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2613_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2613_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
if (lean_obj_tag(v_a_2559_) == 1)
{
lean_object* v_config_2563_; lean_object* v_val_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2608_; 
v_config_2563_ = lean_ctor_get(v_a_2524_, 0);
v_val_2564_ = lean_ctor_get(v_a_2559_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_a_2559_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2566_ = v_a_2559_;
v_isShared_2567_ = v_isSharedCheck_2608_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_val_2564_);
lean_dec(v_a_2559_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2608_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
uint8_t v_warnExponents_2568_; lean_object* v___x_2569_; 
v_warnExponents_2568_ = lean_ctor_get_uint8(v_config_2563_, sizeof(void*)*3 + 25);
lean_inc(v_val_2564_);
v___x_2569_ = l_Lean_checkExponent(v_val_2564_, v_warnExponents_2568_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2599_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2599_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2599_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___y_2575_; uint8_t v___x_2582_; 
v___x_2582_ = lean_unbox(v_a_2570_);
lean_dec(v_a_2570_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_del_object(v___x_2572_);
lean_del_object(v___x_2566_);
lean_dec(v_val_2564_);
lean_dec(v_val_2557_);
v___x_2583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2583_);
v___x_2585_ = v___x_2561_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
lean_del_object(v___x_2561_);
v___x_2587_ = l_Int_pow(v_val_2557_, v_val_2564_);
lean_dec(v_val_2564_);
lean_dec(v_val_2557_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_2589_ = lean_int_dec_le(v___x_2588_, v___x_2587_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_2591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_2592_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_2593_ = lean_int_neg(v___x_2587_);
lean_dec(v___x_2587_);
v___x_2594_ = l_Int_toNat(v___x_2593_);
lean_dec(v___x_2593_);
v___x_2595_ = l_Lean_instToExprInt_mkNat(v___x_2594_);
v___x_2596_ = l_Lean_mkApp3(v___x_2590_, v___x_2591_, v___x_2592_, v___x_2595_);
v___y_2575_ = v___x_2596_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = l_Int_toNat(v___x_2587_);
lean_dec(v___x_2587_);
v___x_2598_ = l_Lean_instToExprInt_mkNat(v___x_2597_);
v___y_2575_ = v___x_2598_;
goto v___jp_2574_;
}
}
v___jp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2575_);
v___x_2577_ = v___x_2566_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___y_2575_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2577_);
v___x_2579_ = v___x_2572_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_del_object(v___x_2566_);
lean_dec(v_val_2564_);
lean_del_object(v___x_2561_);
lean_dec(v_val_2557_);
v_a_2600_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2569_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2569_);
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
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_dec(v_a_2559_);
lean_dec(v_val_2557_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2609_);
v___x_2611_ = v___x_2561_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_val_2557_);
v_a_2614_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2558_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2558_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
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
lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_dec(v_a_2553_);
lean_dec_ref(v_arg_2537_);
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2622_);
v___x_2624_ = v___x_2555_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_arg_2537_);
v_a_2627_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2552_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2552_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
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
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_a_2635_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2533_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2533_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
v___jp_2530_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___redArg___boxed(lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Int_reducePow___redArg(v_e_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec_ref(v_a_2644_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow(lean_object* v_e_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Int_reducePow___redArg(v_e_2651_, v_a_2653_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Int_reducePow___boxed(lean_object* v_e_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Int_reducePow(v_e_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2700_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2701_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2698_, v___x_2699_, v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30____boxed(lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_();
return v_res_2703_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_alloc_closure((void*)(l_Int_reducePow___boxed), 9, 0);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_(){
_start:
{
lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2708_ = 1;
v___x_2709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_);
v___x_2710_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2707_, v___x_2708_, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32____boxed(lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_();
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_(){
_start:
{
lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reducePow_declare__92___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_30_));
v___x_2715_ = 1;
v___x_2716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_32_);
v___x_2717_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2714_, v___x_2715_, v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34____boxed(lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reducePow___regBuiltin_Int_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2823168041____hygCtx___hyg_34_();
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg(lean_object* v_e_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = ((lean_object*)(l_Int_reduceLT___redArg___closed__2));
v___x_2732_ = lean_unsigned_to_nat(4u);
v___x_2733_ = l_Lean_Expr_isAppOfArity(v_e_2725_, v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_dec_ref(v_e_2725_);
v___x_2734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = l_Lean_Expr_appFn_x21(v_e_2725_);
v___x_2737_ = l_Lean_Expr_appArg_x21(v___x_2736_);
lean_dec_ref(v___x_2736_);
v___x_2738_ = l_Lean_Meta_getIntValue_x3f(v___x_2737_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2770_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2770_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2770_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
if (lean_obj_tag(v_a_2739_) == 1)
{
lean_object* v_val_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_del_object(v___x_2741_);
v_val_2743_ = lean_ctor_get(v_a_2739_, 0);
lean_inc(v_val_2743_);
lean_dec_ref_known(v_a_2739_, 1);
v___x_2744_ = l_Lean_Expr_appArg_x21(v_e_2725_);
v___x_2745_ = l_Lean_Meta_getIntValue_x3f(v___x_2744_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2757_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
if (lean_obj_tag(v_a_2746_) == 1)
{
lean_object* v_val_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; 
lean_del_object(v___x_2748_);
v_val_2750_ = lean_ctor_get(v_a_2746_, 0);
lean_inc(v_val_2750_);
lean_dec_ref_known(v_a_2746_, 1);
v___x_2751_ = lean_int_dec_lt(v_val_2743_, v_val_2750_);
lean_dec(v_val_2750_);
lean_dec(v_val_2743_);
v___x_2752_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2725_, v___x_2751_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec(v_a_2746_);
lean_dec(v_val_2743_);
lean_dec_ref(v_e_2725_);
v___x_2753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2753_);
v___x_2755_ = v___x_2748_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_val_2743_);
lean_dec_ref(v_e_2725_);
v_a_2758_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2745_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2745_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2725_);
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2766_);
v___x_2768_ = v___x_2741_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v_e_2725_);
v_a_2771_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2738_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2738_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___redArg___boxed(lean_object* v_e_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Int_reduceLT___redArg(v_e_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT(lean_object* v_e_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Int_reduceLT___redArg(v_e_2786_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLT___boxed(lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Int_reduceLT(v_e_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2826_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2827_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2824_, v___x_2825_, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27____boxed(lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_();
return v_res_2829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_alloc_closure((void*)(l_Int_reduceLT___boxed), 9, 0);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2834_ = 1;
v___x_2835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_);
v___x_2836_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2833_, v___x_2834_, v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29____boxed(lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_();
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_2841_ = 1;
v___x_2842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_29_);
v___x_2843_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2840_, v___x_2841_, v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31____boxed(lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLT___regBuiltin_Int_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_31_();
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg(lean_object* v_e_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = ((lean_object*)(l_Int_reduceLE___redArg___closed__2));
v___x_2858_ = lean_unsigned_to_nat(4u);
v___x_2859_ = l_Lean_Expr_isAppOfArity(v_e_2851_, v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec_ref(v_e_2851_);
v___x_2860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = l_Lean_Expr_appFn_x21(v_e_2851_);
v___x_2863_ = l_Lean_Expr_appArg_x21(v___x_2862_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = l_Lean_Meta_getIntValue_x3f(v___x_2863_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2896_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2896_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2896_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
if (lean_obj_tag(v_a_2865_) == 1)
{
lean_object* v_val_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_del_object(v___x_2867_);
v_val_2869_ = lean_ctor_get(v_a_2865_, 0);
lean_inc(v_val_2869_);
lean_dec_ref_known(v_a_2865_, 1);
v___x_2870_ = l_Lean_Expr_appArg_x21(v_e_2851_);
v___x_2871_ = l_Lean_Meta_getIntValue_x3f(v___x_2870_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2883_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
if (lean_obj_tag(v_a_2872_) == 1)
{
lean_object* v_val_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; 
lean_del_object(v___x_2874_);
v_val_2876_ = lean_ctor_get(v_a_2872_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v_a_2872_, 1);
v___x_2877_ = lean_int_dec_le(v_val_2869_, v_val_2876_);
lean_dec(v_val_2876_);
lean_dec(v_val_2869_);
v___x_2878_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2851_, v___x_2877_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_dec(v_a_2872_);
lean_dec(v_val_2869_);
lean_dec_ref(v_e_2851_);
v___x_2879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2879_);
v___x_2881_ = v___x_2874_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_val_2869_);
lean_dec_ref(v_e_2851_);
v_a_2884_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2871_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2871_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_dec(v_a_2865_);
lean_dec_ref(v_e_2851_);
v___x_2892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2892_);
v___x_2894_ = v___x_2867_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v_e_2851_);
v_a_2897_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2864_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2864_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___redArg___boxed(lean_object* v_e_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Int_reduceLE___redArg(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE(lean_object* v_e_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Int_reduceLE___redArg(v_e_2912_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceLE___boxed(lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Int_reduceLE(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2952_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2953_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2950_, v___x_2951_, v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27____boxed(lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_();
return v_res_2955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_alloc_closure((void*)(l_Int_reduceLE___boxed), 9, 0);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2960_ = 1;
v___x_2961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_);
v___x_2962_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2959_, v___x_2960_, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29____boxed(lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_();
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_2967_ = 1;
v___x_2968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_29_);
v___x_2969_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2966_, v___x_2967_, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31____boxed(lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceLE___regBuiltin_Int_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_31_();
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg(lean_object* v_e_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2983_ = ((lean_object*)(l_Int_reduceGT___redArg___closed__2));
v___x_2984_ = lean_unsigned_to_nat(4u);
v___x_2985_ = l_Lean_Expr_isAppOfArity(v_e_2977_, v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref(v_e_2977_);
v___x_2986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = l_Lean_Expr_appFn_x21(v_e_2977_);
v___x_2989_ = l_Lean_Expr_appArg_x21(v___x_2988_);
lean_dec_ref(v___x_2988_);
v___x_2990_ = l_Lean_Meta_getIntValue_x3f(v___x_2989_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3022_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3022_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3022_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
if (lean_obj_tag(v_a_2991_) == 1)
{
lean_object* v_val_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_del_object(v___x_2993_);
v_val_2995_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v_a_2991_, 1);
v___x_2996_ = l_Lean_Expr_appArg_x21(v_e_2977_);
v___x_2997_ = l_Lean_Meta_getIntValue_x3f(v___x_2996_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3009_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
if (lean_obj_tag(v_a_2998_) == 1)
{
lean_object* v_val_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; 
lean_del_object(v___x_3000_);
v_val_3002_ = lean_ctor_get(v_a_2998_, 0);
lean_inc(v_val_3002_);
lean_dec_ref_known(v_a_2998_, 1);
v___x_3003_ = lean_int_dec_lt(v_val_3002_, v_val_2995_);
lean_dec(v_val_2995_);
lean_dec(v_val_3002_);
v___x_3004_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2977_, v___x_3003_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
lean_dec(v_a_2998_);
lean_dec(v_val_2995_);
lean_dec_ref(v_e_2977_);
v___x_3005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3005_);
v___x_3007_ = v___x_3000_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_val_2995_);
lean_dec_ref(v_e_2977_);
v_a_3010_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2997_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2997_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
lean_dec(v_a_2991_);
lean_dec_ref(v_e_2977_);
v___x_3018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3018_);
v___x_3020_ = v___x_2993_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v_e_2977_);
v_a_3023_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2990_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2990_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___redArg___boxed(lean_object* v_e_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Int_reduceGT___redArg(v_e_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT(lean_object* v_e_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Int_reduceGT___redArg(v_e_3038_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGT___boxed(lean_object* v_e_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Int_reduceGT(v_e_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLT_declare__97___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2257538243____hygCtx___hyg_27_));
v___x_3065_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3066_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3063_, v___x_3064_, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27____boxed(lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_();
return v_res_3068_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_alloc_closure((void*)(l_Int_reduceGT___boxed), 9, 0);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3073_ = 1;
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_);
v___x_3075_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3072_, v___x_3073_, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29____boxed(lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_();
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGT_declare__107___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_27_));
v___x_3080_ = 1;
v___x_3081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_29_);
v___x_3082_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3079_, v___x_3080_, v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31____boxed(lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGT___regBuiltin_Int_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_958370554____hygCtx___hyg_31_();
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg(lean_object* v_e_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3096_ = ((lean_object*)(l_Int_reduceGE___redArg___closed__2));
v___x_3097_ = lean_unsigned_to_nat(4u);
v___x_3098_ = l_Lean_Expr_isAppOfArity(v_e_3090_, v___x_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec_ref(v_e_3090_);
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = l_Lean_Expr_appFn_x21(v_e_3090_);
v___x_3102_ = l_Lean_Expr_appArg_x21(v___x_3101_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = l_Lean_Meta_getIntValue_x3f(v___x_3102_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3135_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3135_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3135_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
if (lean_obj_tag(v_a_3104_) == 1)
{
lean_object* v_val_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_del_object(v___x_3106_);
v_val_3108_ = lean_ctor_get(v_a_3104_, 0);
lean_inc(v_val_3108_);
lean_dec_ref_known(v_a_3104_, 1);
v___x_3109_ = l_Lean_Expr_appArg_x21(v_e_3090_);
v___x_3110_ = l_Lean_Meta_getIntValue_x3f(v___x_3109_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3122_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3122_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3122_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
if (lean_obj_tag(v_a_3111_) == 1)
{
lean_object* v_val_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; 
lean_del_object(v___x_3113_);
v_val_3115_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v_a_3111_, 1);
v___x_3116_ = lean_int_dec_le(v_val_3115_, v_val_3108_);
lean_dec(v_val_3108_);
lean_dec(v_val_3115_);
v___x_3117_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3090_, v___x_3116_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
lean_dec(v_a_3111_);
lean_dec(v_val_3108_);
lean_dec_ref(v_e_3090_);
v___x_3118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3118_);
v___x_3120_ = v___x_3113_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_val_3108_);
lean_dec_ref(v_e_3090_);
v_a_3123_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3110_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3110_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3090_);
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3131_);
v___x_3133_ = v___x_3106_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_e_3090_);
v_a_3136_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3103_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3103_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___redArg___boxed(lean_object* v_e_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Int_reduceGE___redArg(v_e_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE(lean_object* v_e_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Int_reduceGE___redArg(v_e_3151_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceGE___boxed(lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Int_reduceGE(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceLE_declare__102___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2835252116____hygCtx___hyg_27_));
v___x_3178_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3179_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3176_, v___x_3177_, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27____boxed(lean_object* v_a_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_();
return v_res_3181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_alloc_closure((void*)(l_Int_reduceGE___boxed), 9, 0);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3186_ = 1;
v___x_3187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_);
v___x_3188_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3185_, v___x_3186_, v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29____boxed(lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_();
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3192_; uint8_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceGE_declare__112___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_27_));
v___x_3193_ = 1;
v___x_3194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_29_);
v___x_3195_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3192_, v___x_3193_, v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31____boxed(lean_object* v_a_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceGE___regBuiltin_Int_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1048714272____hygCtx___hyg_31_();
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg(lean_object* v_e_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3207_ = ((lean_object*)(l_Int_reduceEq___redArg___closed__1));
v___x_3208_ = lean_unsigned_to_nat(3u);
v___x_3209_ = l_Lean_Expr_isAppOfArity(v_e_3201_, v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v_e_3201_);
v___x_3210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = l_Lean_Expr_appFn_x21(v_e_3201_);
v___x_3213_ = l_Lean_Expr_appArg_x21(v___x_3212_);
lean_dec_ref(v___x_3212_);
v___x_3214_ = l_Lean_Meta_getIntValue_x3f(v___x_3213_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3246_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3246_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3246_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
if (lean_obj_tag(v_a_3215_) == 1)
{
lean_object* v_val_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_del_object(v___x_3217_);
v_val_3219_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_val_3219_);
lean_dec_ref_known(v_a_3215_, 1);
v___x_3220_ = l_Lean_Expr_appArg_x21(v_e_3201_);
v___x_3221_ = l_Lean_Meta_getIntValue_x3f(v___x_3220_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3233_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
if (lean_obj_tag(v_a_3222_) == 1)
{
lean_object* v_val_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; 
lean_del_object(v___x_3224_);
v_val_3226_ = lean_ctor_get(v_a_3222_, 0);
lean_inc(v_val_3226_);
lean_dec_ref_known(v_a_3222_, 1);
v___x_3227_ = lean_int_dec_eq(v_val_3219_, v_val_3226_);
lean_dec(v_val_3226_);
lean_dec(v_val_3219_);
v___x_3228_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3201_, v___x_3227_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_dec(v_a_3222_);
lean_dec(v_val_3219_);
lean_dec_ref(v_e_3201_);
v___x_3229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3229_);
v___x_3231_ = v___x_3224_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_val_3219_);
lean_dec_ref(v_e_3201_);
v_a_3234_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3221_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3221_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec(v_a_3215_);
lean_dec_ref(v_e_3201_);
v___x_3242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3242_);
v___x_3244_ = v___x_3217_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_e_3201_);
v_a_3247_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3214_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3214_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___redArg___boxed(lean_object* v_e_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Int_reduceEq___redArg(v_e_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq(lean_object* v_e_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Int_reduceEq___redArg(v_e_3262_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceEq___boxed(lean_object* v_e_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Int_reduceEq(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3301_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3302_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3299_, v___x_3300_, v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27____boxed(lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_();
return v_res_3304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_alloc_closure((void*)(l_Int_reduceEq___boxed), 9, 0);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3309_ = 1;
v___x_3310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_);
v___x_3311_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3308_, v___x_3309_, v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29____boxed(lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_();
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceEq_declare__117___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_27_));
v___x_3316_ = 1;
v___x_3317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_29_);
v___x_3318_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3315_, v___x_3316_, v___x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31____boxed(lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceEq___regBuiltin_Int_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1701374538____hygCtx___hyg_31_();
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg(lean_object* v_e_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3330_ = ((lean_object*)(l_Int_reduceNe___redArg___closed__1));
v___x_3331_ = lean_unsigned_to_nat(3u);
v___x_3332_ = l_Lean_Expr_isAppOfArity(v_e_3324_, v___x_3330_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec_ref(v_e_3324_);
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = l_Lean_Expr_appFn_x21(v_e_3324_);
v___x_3336_ = l_Lean_Expr_appArg_x21(v___x_3335_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = l_Lean_Meta_getIntValue_x3f(v___x_3336_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3371_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3371_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3371_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_a_3338_) == 1)
{
lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_del_object(v___x_3340_);
v_val_3342_ = lean_ctor_get(v_a_3338_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v_a_3338_, 1);
v___x_3343_ = l_Lean_Expr_appArg_x21(v_e_3324_);
v___x_3344_ = l_Lean_Meta_getIntValue_x3f(v___x_3343_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3358_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3347_ = v___x_3344_;
v_isShared_3348_ = v_isSharedCheck_3358_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3358_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
if (lean_obj_tag(v_a_3345_) == 1)
{
lean_object* v_val_3349_; uint8_t v___x_3350_; 
lean_del_object(v___x_3347_);
v_val_3349_ = lean_ctor_get(v_a_3345_, 0);
lean_inc(v_val_3349_);
lean_dec_ref_known(v_a_3345_, 1);
v___x_3350_ = lean_int_dec_eq(v_val_3342_, v_val_3349_);
lean_dec(v_val_3349_);
lean_dec(v_val_3342_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3324_, v___x_3332_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
return v___x_3351_;
}
else
{
uint8_t v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = 0;
v___x_3353_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_3324_, v___x_3352_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
return v___x_3353_;
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_a_3345_);
lean_dec(v_val_3342_);
lean_dec_ref(v_e_3324_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3354_);
v___x_3356_ = v___x_3347_;
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
lean_dec(v_val_3342_);
lean_dec_ref(v_e_3324_);
v_a_3359_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3344_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3344_);
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
else
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
lean_dec(v_a_3338_);
lean_dec_ref(v_e_3324_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3367_);
v___x_3369_ = v___x_3340_;
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
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec_ref(v_e_3324_);
v_a_3372_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3337_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3337_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___redArg___boxed(lean_object* v_e_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Int_reduceNe___redArg(v_e_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe(lean_object* v_e_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Int_reduceNe___redArg(v_e_3387_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNe___boxed(lean_object* v_e_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Int_reduceNe(v_e_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3431_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3432_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3429_, v___x_3430_, v___x_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27____boxed(lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_();
return v_res_3434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_alloc_closure((void*)(l_Int_reduceNe___boxed), 9, 0);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3439_ = 1;
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_);
v___x_3441_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3438_, v___x_3439_, v___x_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29____boxed(lean_object* v_a_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_();
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNe_declare__122___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_27_));
v___x_3446_ = 1;
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_29_);
v___x_3448_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3445_, v___x_3446_, v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31____boxed(lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNe___regBuiltin_Int_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_30627056____hygCtx___hyg_31_();
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg(lean_object* v_e_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v___x_3462_ = ((lean_object*)(l_Int_reduceBEq___redArg___closed__2));
v___x_3463_ = lean_unsigned_to_nat(4u);
v___x_3464_ = l_Lean_Expr_isAppOfArity(v_e_3456_, v___x_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
return v___x_3466_;
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = l_Lean_Expr_appFn_x21(v_e_3456_);
v___x_3468_ = l_Lean_Expr_appArg_x21(v___x_3467_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = l_Lean_Meta_getIntValue_x3f(v___x_3468_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3514_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3514_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3514_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
if (lean_obj_tag(v_a_3470_) == 1)
{
lean_object* v_val_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3509_; 
v_val_3474_ = lean_ctor_get(v_a_3470_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3470_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3476_ = v_a_3470_;
v_isShared_3477_ = v_isSharedCheck_3509_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_val_3474_);
lean_dec(v_a_3470_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3509_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = l_Lean_Expr_appArg_x21(v_e_3456_);
v___x_3479_ = l_Lean_Meta_getIntValue_x3f(v___x_3478_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3500_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3500_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3500_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___y_3485_; 
if (lean_obj_tag(v_a_3480_) == 1)
{
lean_object* v_val_3492_; uint8_t v___x_3493_; 
lean_del_object(v___x_3472_);
v_val_3492_ = lean_ctor_get(v_a_3480_, 0);
lean_inc(v_val_3492_);
lean_dec_ref_known(v_a_3480_, 1);
v___x_3493_ = lean_int_dec_eq(v_val_3474_, v_val_3492_);
lean_dec(v_val_3492_);
lean_dec(v_val_3474_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_3485_ = v___x_3494_;
goto v___jp_3484_;
}
else
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_3485_ = v___x_3495_;
goto v___jp_3484_;
}
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
lean_del_object(v___x_3482_);
lean_dec(v_a_3480_);
lean_del_object(v___x_3476_);
lean_dec(v_val_3474_);
v___x_3496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3496_);
v___x_3498_ = v___x_3472_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
v___jp_3484_:
{
lean_object* v___x_3487_; 
lean_inc_ref(v___y_3485_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set_tag(v___x_3476_, 0);
lean_ctor_set(v___x_3476_, 0, v___y_3485_);
v___x_3487_ = v___x_3476_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___y_3485_);
v___x_3487_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3489_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3487_);
v___x_3489_ = v___x_3482_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_del_object(v___x_3476_);
lean_dec(v_val_3474_);
lean_del_object(v___x_3472_);
v_a_3501_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3479_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3479_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
lean_dec(v_a_3470_);
v___x_3510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3510_);
v___x_3512_ = v___x_3472_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
v_a_3515_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3469_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3469_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
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
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___redArg___boxed(lean_object* v_e_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Int_reduceBEq___redArg(v_e_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec_ref(v_e_3523_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq(lean_object* v_e_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Int_reduceBEq___redArg(v_e_3530_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBEq___boxed(lean_object* v_e_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Int_reduceBEq(v_e_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
lean_dec(v_a_3541_);
lean_dec_ref(v_e_3540_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3570_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3571_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3568_, v___x_3569_, v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27____boxed(lean_object* v_a_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_();
return v_res_3573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = lean_alloc_closure((void*)(l_Int_reduceBEq___boxed), 9, 0);
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3578_ = 1;
v___x_3579_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_);
v___x_3580_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3577_, v___x_3578_, v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29____boxed(lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_();
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3584_; uint8_t v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBEq_declare__127___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_27_));
v___x_3585_ = 1;
v___x_3586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_29_);
v___x_3587_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3584_, v___x_3585_, v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31____boxed(lean_object* v_a_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBEq___regBuiltin_Int_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3351316741____hygCtx___hyg_31_();
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg(lean_object* v_e_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3599_ = ((lean_object*)(l_Int_reduceBNe___redArg___closed__1));
v___x_3600_ = lean_unsigned_to_nat(4u);
v___x_3601_ = l_Lean_Expr_isAppOfArity(v_e_3593_, v___x_3599_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = l_Lean_Expr_appFn_x21(v_e_3593_);
v___x_3605_ = l_Lean_Expr_appArg_x21(v___x_3604_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = l_Lean_Meta_getIntValue_x3f(v___x_3605_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3652_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3652_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3652_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3647_; 
v_val_3611_ = lean_ctor_get(v_a_3607_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_a_3607_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3613_ = v_a_3607_;
v_isShared_3614_ = v_isSharedCheck_3647_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_val_3611_);
lean_dec(v_a_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3647_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = l_Lean_Expr_appArg_x21(v_e_3593_);
v___x_3616_ = l_Lean_Meta_getIntValue_x3f(v___x_3615_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3638_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3638_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3638_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___y_3622_; 
if (lean_obj_tag(v_a_3617_) == 1)
{
lean_object* v_val_3631_; uint8_t v___x_3632_; 
lean_del_object(v___x_3609_);
v_val_3631_ = lean_ctor_get(v_a_3617_, 0);
lean_inc(v_val_3631_);
lean_dec_ref_known(v_a_3617_, 1);
v___x_3632_ = lean_int_dec_eq(v_val_3611_, v_val_3631_);
lean_dec(v_val_3631_);
lean_dec(v_val_3611_);
if (v___x_3632_ == 0)
{
if (v___x_3601_ == 0)
{
goto v___jp_3629_;
}
else
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__6);
v___y_3622_ = v___x_3633_;
goto v___jp_3621_;
}
}
else
{
goto v___jp_3629_;
}
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_del_object(v___x_3619_);
lean_dec(v_a_3617_);
lean_del_object(v___x_3613_);
lean_dec(v_val_3611_);
v___x_3634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3634_);
v___x_3636_ = v___x_3609_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
v___jp_3621_:
{
lean_object* v___x_3624_; 
lean_inc_ref(v___y_3622_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 0);
lean_ctor_set(v___x_3613_, 0, v___y_3622_);
v___x_3624_ = v___x_3613_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___y_3622_);
v___x_3624_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3626_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v___x_3624_);
v___x_3626_ = v___x_3619_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
v___jp_3629_:
{
lean_object* v___x_3630_; 
v___x_3630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBoolPred___redArg___closed__3);
v___y_3622_ = v___x_3630_;
goto v___jp_3621_;
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_del_object(v___x_3613_);
lean_dec(v_val_3611_);
lean_del_object(v___x_3609_);
v_a_3639_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3616_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3616_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
lean_dec(v_a_3607_);
v___x_3648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3648_);
v___x_3650_ = v___x_3609_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
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
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3606_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3606_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___redArg___boxed(lean_object* v_e_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Int_reduceBNe___redArg(v_e_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec_ref(v_e_3661_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe(lean_object* v_e_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Int_reduceBNe___redArg(v_e_3668_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceBNe___boxed(lean_object* v_e_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Int_reduceBNe(v_e_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_e_3678_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3708_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3709_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3706_, v___x_3707_, v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27____boxed(lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_();
return v_res_3711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_alloc_closure((void*)(l_Int_reduceBNe___boxed), 9, 0);
v___x_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_3715_; uint8_t v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3716_ = 1;
v___x_3717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_);
v___x_3718_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3715_, v___x_3716_, v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29____boxed(lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_();
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceBNe_declare__132___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_27_));
v___x_3723_ = 1;
v___x_3724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_29_);
v___x_3725_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3722_, v___x_3723_, v___x_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31____boxed(lean_object* v_a_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBNe___regBuiltin_Int_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_748548922____hygCtx___hyg_31_();
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(lean_object* v_declName_3728_, lean_object* v_op_3729_, lean_object* v_e_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = lean_unsigned_to_nat(1u);
v___x_3737_ = l_Lean_Expr_isAppOfArity(v_e_3730_, v_declName_3728_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref(v_op_3729_);
v___x_3738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = l_Lean_Expr_appArg_x21(v_e_3730_);
v___x_3741_ = l_Lean_Meta_getIntValue_x3f(v___x_3740_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3763_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3763_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3763_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
if (lean_obj_tag(v_a_3742_) == 1)
{
lean_object* v_val_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3758_; 
v_val_3746_ = lean_ctor_get(v_a_3742_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3742_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3748_ = v_a_3742_;
v_isShared_3749_ = v_isSharedCheck_3758_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_val_3746_);
lean_dec(v_a_3742_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3758_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3750_ = lean_apply_1(v_op_3729_, v_val_3746_);
v___x_3751_ = l_Lean_mkNatLit(v___x_3750_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set_tag(v___x_3748_, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3751_);
v___x_3753_ = v___x_3748_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3753_);
v___x_3755_ = v___x_3744_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_dec(v_a_3742_);
lean_dec_ref(v_op_3729_);
v___x_3759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3759_);
v___x_3761_ = v___x_3744_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v_op_3729_);
v_a_3764_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3741_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3741_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg___boxed(lean_object* v_declName_3772_, lean_object* v_op_3773_, lean_object* v_e_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___redArg(v_declName_3772_, v_op_3773_, v_e_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec_ref(v_e_3774_);
lean_dec(v_declName_3772_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(lean_object* v_declName_3781_, lean_object* v_op_3782_, lean_object* v_e_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = lean_unsigned_to_nat(1u);
v___x_3793_ = l_Lean_Expr_isAppOfArity(v_e_3783_, v_declName_3781_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_dec_ref(v_op_3782_);
v___x_3794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
return v___x_3795_;
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = l_Lean_Expr_appArg_x21(v_e_3783_);
v___x_3797_ = l_Lean_Meta_getIntValue_x3f(v___x_3796_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3819_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3819_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3819_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
if (lean_obj_tag(v_a_3798_) == 1)
{
lean_object* v_val_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3814_; 
v_val_3802_ = lean_ctor_get(v_a_3798_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_a_3798_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3804_ = v_a_3798_;
v_isShared_3805_ = v_isSharedCheck_3814_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_val_3802_);
lean_dec(v_a_3798_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3814_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3806_ = lean_apply_1(v_op_3782_, v_val_3802_);
v___x_3807_ = l_Lean_mkNatLit(v___x_3806_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set_tag(v___x_3804_, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3807_);
v___x_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3809_);
v___x_3811_ = v___x_3800_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec(v_a_3798_);
lean_dec_ref(v_op_3782_);
v___x_3815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3815_);
v___x_3817_ = v___x_3800_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_op_3782_);
v_a_3820_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3797_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3797_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore___boxed(lean_object* v_declName_3828_, lean_object* v_op_3829_, lean_object* v_e_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCore(v_declName_3828_, v_op_3829_, v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_e_3830_);
lean_dec(v_declName_3828_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg(lean_object* v_e_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3850_ = ((lean_object*)(l_Int_reduceAbs___redArg___closed__1));
v___x_3851_ = lean_unsigned_to_nat(1u);
v___x_3852_ = l_Lean_Expr_isAppOfArity(v_e_3844_, v___x_3850_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = l_Lean_Expr_appArg_x21(v_e_3844_);
v___x_3856_ = l_Lean_Meta_getIntValue_x3f(v___x_3855_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3878_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3878_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3878_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
if (lean_obj_tag(v_a_3857_) == 1)
{
lean_object* v_val_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3873_; 
v_val_3861_ = lean_ctor_get(v_a_3857_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_a_3857_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3863_ = v_a_3857_;
v_isShared_3864_ = v_isSharedCheck_3873_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_val_3861_);
lean_dec(v_a_3857_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3873_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3865_ = lean_nat_abs(v_val_3861_);
lean_dec(v_val_3861_);
v___x_3866_ = l_Lean_mkNatLit(v___x_3865_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3866_);
v___x_3868_ = v___x_3863_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3870_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3868_);
v___x_3870_ = v___x_3859_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
lean_dec(v_a_3857_);
v___x_3874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3874_);
v___x_3876_ = v___x_3859_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_a_3879_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3856_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3856_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___redArg___boxed(lean_object* v_e_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Int_reduceAbs___redArg(v_e_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec_ref(v_a_3888_);
lean_dec_ref(v_e_3887_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs(lean_object* v_e_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Int_reduceAbs___redArg(v_e_3894_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceAbs___boxed(lean_object* v_e_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Int_reduceAbs(v_e_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_e_3904_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3930_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3931_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3928_, v___x_3929_, v___x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20____boxed(lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_();
return v_res_3933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_alloc_closure((void*)(l_Int_reduceAbs___boxed), 9, 0);
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3937_; uint8_t v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3938_ = 1;
v___x_3939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_);
v___x_3940_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3937_, v___x_3938_, v___x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22____boxed(lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_();
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceAbs_declare__140___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_20_));
v___x_3945_ = 1;
v___x_3946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_22_);
v___x_3947_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3944_, v___x_3945_, v___x_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24____boxed(lean_object* v_a_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceAbs___regBuiltin_Int_reduceAbs_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_1548991167____hygCtx___hyg_24_();
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg(lean_object* v_e_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3960_ = ((lean_object*)(l_Int_reduceToNat___redArg___closed__1));
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = l_Lean_Expr_isAppOfArity(v_e_3954_, v___x_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = l_Lean_Expr_appArg_x21(v_e_3954_);
v___x_3966_ = l_Lean_Meta_getIntValue_x3f(v___x_3965_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3988_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3988_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3988_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
if (lean_obj_tag(v_a_3967_) == 1)
{
lean_object* v_val_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3983_; 
v_val_3971_ = lean_ctor_get(v_a_3967_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_a_3967_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3973_ = v_a_3967_;
v_isShared_3974_ = v_isSharedCheck_3983_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_val_3971_);
lean_dec(v_a_3967_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3983_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3975_ = l_Int_toNat(v_val_3971_);
lean_dec(v_val_3971_);
v___x_3976_ = l_Lean_mkNatLit(v___x_3975_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set_tag(v___x_3973_, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3976_);
v___x_3978_ = v___x_3973_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3980_; 
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3978_);
v___x_3980_ = v___x_3969_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
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
else
{
lean_object* v___x_3984_; lean_object* v___x_3986_; 
lean_dec(v_a_3967_);
v___x_3984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3984_);
v___x_3986_ = v___x_3969_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3966_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3966_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___redArg___boxed(lean_object* v_e_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Int_reduceToNat___redArg(v_e_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec_ref(v_e_3997_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat(lean_object* v_e_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Int_reduceToNat___redArg(v_e_4004_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceToNat___boxed(lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Int_reduceToNat(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_e_4014_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4040_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4041_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4038_, v___x_4039_, v___x_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20____boxed(lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_();
return v_res_4043_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = lean_alloc_closure((void*)(l_Int_reduceToNat___boxed), 9, 0);
v___x_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4047_; uint8_t v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4048_ = 1;
v___x_4049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_);
v___x_4050_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4047_, v___x_4048_, v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22____boxed(lean_object* v_a_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_();
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceToNat_declare__145___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_20_));
v___x_4055_ = 1;
v___x_4056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_22_);
v___x_4057_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4054_, v___x_4055_, v___x_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24____boxed(lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceToNat___regBuiltin_Int_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_3578908840____hygCtx___hyg_24_();
return v_res_4059_;
}
}
static lean_object* _init_l_Int_reduceNegSucc___redArg___closed__2(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_unsigned_to_nat(1u);
v___x_4065_ = lean_nat_to_int(v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg(lean_object* v_e_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4066_, v_a_4068_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4126_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4126_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4126_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; uint8_t v___x_4081_; 
v___x_4080_ = l_Lean_Expr_cleanupAnnotations(v_a_4076_);
v___x_4081_ = l_Lean_Expr_isApp(v___x_4080_);
if (v___x_4081_ == 0)
{
lean_dec_ref(v___x_4080_);
lean_del_object(v___x_4078_);
goto v___jp_4072_;
}
else
{
lean_object* v_arg_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; 
v_arg_4082_ = lean_ctor_get(v___x_4080_, 1);
lean_inc_ref(v_arg_4082_);
v___x_4083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4080_);
v___x_4084_ = ((lean_object*)(l_Int_reduceNegSucc___redArg___closed__1));
v___x_4085_ = l_Lean_Expr_isConstOf(v___x_4083_, v___x_4084_);
lean_dec_ref(v___x_4083_);
if (v___x_4085_ == 0)
{
lean_dec_ref(v_arg_4082_);
lean_del_object(v___x_4078_);
goto v___jp_4072_;
}
else
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Lean_Meta_getNatValue_x3f(v_arg_4082_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec_ref(v_arg_4082_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4117_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4117_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4117_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___y_4092_; 
if (lean_obj_tag(v_a_4087_) == 1)
{
lean_object* v_val_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
lean_del_object(v___x_4078_);
v_val_4097_ = lean_ctor_get(v_a_4087_, 0);
lean_inc(v_val_4097_);
lean_dec_ref_known(v_a_4087_, 1);
v___x_4098_ = lean_nat_to_int(v_val_4097_);
v___x_4099_ = lean_obj_once(&l_Int_reduceNegSucc___redArg___closed__2, &l_Int_reduceNegSucc___redArg___closed__2_once, _init_l_Int_reduceNegSucc___redArg___closed__2);
v___x_4100_ = lean_int_add(v___x_4098_, v___x_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_int_neg(v___x_4100_);
lean_dec(v___x_4100_);
v___x_4102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4103_ = lean_int_dec_le(v___x_4102_, v___x_4101_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4104_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4107_ = lean_int_neg(v___x_4101_);
lean_dec(v___x_4101_);
v___x_4108_ = l_Int_toNat(v___x_4107_);
lean_dec(v___x_4107_);
v___x_4109_ = l_Lean_instToExprInt_mkNat(v___x_4108_);
v___x_4110_ = l_Lean_mkApp3(v___x_4104_, v___x_4105_, v___x_4106_, v___x_4109_);
v___y_4092_ = v___x_4110_;
goto v___jp_4091_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = l_Int_toNat(v___x_4101_);
lean_dec(v___x_4101_);
v___x_4112_ = l_Lean_instToExprInt_mkNat(v___x_4111_);
v___y_4092_ = v___x_4112_;
goto v___jp_4091_;
}
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
lean_del_object(v___x_4089_);
lean_dec(v_a_4087_);
v___x_4113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 0, v___x_4113_);
v___x_4115_ = v___x_4078_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
v___jp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___y_4092_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4093_);
v___x_4095_ = v___x_4089_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_del_object(v___x_4078_);
v_a_4118_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4086_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4086_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
v_a_4127_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4075_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4075_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
v___jp_4072_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___redArg___boxed(lean_object* v_e_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Int_reduceNegSucc___redArg(v_e_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc(lean_object* v_e_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Int_reduceNegSucc___redArg(v_e_4142_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNegSucc___boxed(lean_object* v_e_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Int_reduceNegSucc(v_e_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4178_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4179_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4176_, v___x_4177_, v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20____boxed(lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_();
return v_res_4181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = lean_alloc_closure((void*)(l_Int_reduceNegSucc___boxed), 9, 0);
v___x_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4186_ = 1;
v___x_4187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_);
v___x_4188_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4185_, v___x_4186_, v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22____boxed(lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_();
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNegSucc_declare__150___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_20_));
v___x_4193_ = 1;
v___x_4194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_22_);
v___x_4195_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4192_, v___x_4193_, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24____boxed(lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNegSucc___regBuiltin_Int_reduceNegSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2011509646____hygCtx___hyg_24_();
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg(lean_object* v_e_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4201_, v_a_4203_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4258_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4258_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4258_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4215_ = l_Lean_Expr_cleanupAnnotations(v_a_4211_);
v___x_4216_ = l_Lean_Expr_isApp(v___x_4215_);
if (v___x_4216_ == 0)
{
lean_dec_ref(v___x_4215_);
lean_del_object(v___x_4213_);
goto v___jp_4207_;
}
else
{
lean_object* v_arg_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v_arg_4217_ = lean_ctor_get(v___x_4215_, 1);
lean_inc_ref(v_arg_4217_);
v___x_4218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4215_);
v___x_4219_ = ((lean_object*)(l_Int_reduceOfNat___redArg___closed__0));
v___x_4220_ = l_Lean_Expr_isConstOf(v___x_4218_, v___x_4219_);
lean_dec_ref(v___x_4218_);
if (v___x_4220_ == 0)
{
lean_dec_ref(v_arg_4217_);
lean_del_object(v___x_4213_);
goto v___jp_4207_;
}
else
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Meta_getNatValue_x3f(v_arg_4217_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec_ref(v_arg_4217_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4249_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4249_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4249_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___y_4227_; 
if (lean_obj_tag(v_a_4222_) == 1)
{
lean_object* v_val_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
lean_del_object(v___x_4213_);
v_val_4232_ = lean_ctor_get(v_a_4222_, 0);
lean_inc(v_val_4232_);
lean_dec_ref_known(v_a_4222_, 1);
v___x_4233_ = lean_nat_to_int(v_val_4232_);
v___x_4234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4235_ = lean_int_dec_le(v___x_4234_, v___x_4233_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4239_ = lean_int_neg(v___x_4233_);
lean_dec(v___x_4233_);
v___x_4240_ = l_Int_toNat(v___x_4239_);
lean_dec(v___x_4239_);
v___x_4241_ = l_Lean_instToExprInt_mkNat(v___x_4240_);
v___x_4242_ = l_Lean_mkApp3(v___x_4236_, v___x_4237_, v___x_4238_, v___x_4241_);
v___y_4227_ = v___x_4242_;
goto v___jp_4226_;
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = l_Int_toNat(v___x_4233_);
lean_dec(v___x_4233_);
v___x_4244_ = l_Lean_instToExprInt_mkNat(v___x_4243_);
v___y_4227_ = v___x_4244_;
goto v___jp_4226_;
}
}
else
{
lean_object* v___x_4245_; lean_object* v___x_4247_; 
lean_del_object(v___x_4224_);
lean_dec(v_a_4222_);
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4245_);
v___x_4247_ = v___x_4213_;
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
v___jp_4226_:
{
lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___y_4227_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4228_);
v___x_4230_ = v___x_4224_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_del_object(v___x_4213_);
v_a_4250_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4221_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4221_);
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
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
v_a_4259_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4210_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4210_);
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
v___jp_4207_:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___redArg___boxed(lean_object* v_e_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Int_reduceOfNat___redArg(v_e_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat(lean_object* v_e_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Int_reduceOfNat___redArg(v_e_4274_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceOfNat___boxed(lean_object* v_e_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Int_reduceOfNat(v_e_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_);
lean_dec(v_a_4291_);
lean_dec_ref(v_a_4290_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4310_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4311_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4308_, v___x_4309_, v___x_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20____boxed(lean_object* v_a_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_();
return v_res_4313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = lean_alloc_closure((void*)(l_Int_reduceOfNat___boxed), 9, 0);
v___x_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4318_ = 1;
v___x_4319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_);
v___x_4320_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4317_, v___x_4318_, v___x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22____boxed(lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_();
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceOfNat_declare__155___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_20_));
v___x_4325_ = 1;
v___x_4326_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_22_);
v___x_4327_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4324_, v___x_4325_, v___x_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24____boxed(lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceOfNat___regBuiltin_Int_reduceOfNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_4198157453____hygCtx___hyg_24_();
return v_res_4329_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = lean_box(0);
v___x_4340_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__4));
v___x_4341_ = l_Lean_mkConst(v___x_4340_, v___x_4339_);
return v___x_4341_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4345_ = lean_box(0);
v___x_4346_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__7));
v___x_4347_ = l_Lean_mkConst(v___x_4346_, v___x_4345_);
return v___x_4347_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_box(0);
v___x_4353_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__10));
v___x_4354_ = l_Lean_mkConst(v___x_4353_, v___x_4352_);
return v___x_4354_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__14(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4358_ = lean_box(0);
v___x_4359_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__13));
v___x_4360_ = l_Lean_mkConst(v___x_4359_, v___x_4358_);
return v___x_4360_;
}
}
static lean_object* _init_l_Int_reduceDvd___redArg___closed__17(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = lean_box(0);
v___x_4366_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__16));
v___x_4367_ = l_Lean_mkConst(v___x_4366_, v___x_4365_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg(lean_object* v_e_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4368_, v_a_4370_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = l_Lean_Expr_cleanupAnnotations(v_a_4378_);
v___x_4380_ = l_Lean_Expr_isApp(v___x_4379_);
if (v___x_4380_ == 0)
{
lean_dec_ref(v___x_4379_);
goto v___jp_4374_;
}
else
{
lean_object* v_arg_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; 
v_arg_4381_ = lean_ctor_get(v___x_4379_, 1);
lean_inc_ref(v_arg_4381_);
v___x_4382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4379_);
v___x_4383_ = l_Lean_Expr_isApp(v___x_4382_);
if (v___x_4383_ == 0)
{
lean_dec_ref(v___x_4382_);
lean_dec_ref(v_arg_4381_);
goto v___jp_4374_;
}
else
{
lean_object* v_arg_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v_arg_4384_ = lean_ctor_get(v___x_4382_, 1);
lean_inc_ref(v_arg_4384_);
v___x_4385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4382_);
v___x_4386_ = l_Lean_Expr_isApp(v___x_4385_);
if (v___x_4386_ == 0)
{
lean_dec_ref(v___x_4385_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
goto v___jp_4374_;
}
else
{
lean_object* v_arg_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v_arg_4387_ = lean_ctor_get(v___x_4385_, 1);
lean_inc_ref(v_arg_4387_);
v___x_4388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4385_);
v___x_4389_ = l_Lean_Expr_isApp(v___x_4388_);
if (v___x_4389_ == 0)
{
lean_dec_ref(v___x_4388_);
lean_dec_ref(v_arg_4387_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
goto v___jp_4374_;
}
else
{
lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4388_);
v___x_4391_ = ((lean_object*)(l_Int_reduceDvd___redArg___closed__2));
v___x_4392_ = l_Lean_Expr_isConstOf(v___x_4390_, v___x_4391_);
lean_dec_ref(v___x_4390_);
if (v___x_4392_ == 0)
{
lean_dec_ref(v_arg_4387_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
goto v___jp_4374_;
}
else
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__5, &l_Int_reduceDvd___redArg___closed__5_once, _init_l_Int_reduceDvd___redArg___closed__5);
v___x_4394_ = l_Lean_Meta_matchesInstance(v_arg_4387_, v___x_4393_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4481_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4481_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4481_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
uint8_t v___x_4399_; 
v___x_4399_ = lean_unbox(v_a_4395_);
lean_dec(v_a_4395_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
v___x_4400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4400_);
v___x_4402_ = v___x_4397_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
else
{
lean_object* v___x_4404_; 
lean_del_object(v___x_4397_);
lean_inc_ref(v_arg_4384_);
v___x_4404_ = l_Lean_Meta_getIntValue_x3f(v_arg_4384_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4472_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4407_ = v___x_4404_;
v_isShared_4408_ = v_isSharedCheck_4472_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4404_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4472_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
if (lean_obj_tag(v_a_4405_) == 1)
{
lean_object* v_val_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4467_; 
lean_del_object(v___x_4407_);
v_val_4409_ = lean_ctor_get(v_a_4405_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_a_4405_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4411_ = v_a_4405_;
v_isShared_4412_ = v_isSharedCheck_4467_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_val_4409_);
lean_dec(v_a_4405_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4467_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; 
lean_inc_ref(v_arg_4381_);
v___x_4413_ = l_Lean_Meta_getIntValue_x3f(v_arg_4381_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4458_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4416_ = v___x_4413_;
v_isShared_4417_ = v_isSharedCheck_4458_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4413_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4458_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
if (lean_obj_tag(v_a_4414_) == 1)
{
lean_object* v_val_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4453_; 
v_val_4418_ = lean_ctor_get(v_a_4414_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v_a_4414_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4420_ = v_a_4414_;
v_isShared_4421_ = v_isSharedCheck_4453_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_val_4418_);
lean_dec(v_a_4414_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4453_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
v___x_4422_ = lean_int_emod(v_val_4418_, v_val_4409_);
lean_dec(v_val_4409_);
lean_dec(v_val_4418_);
v___x_4423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4424_ = lean_int_dec_eq(v___x_4422_, v___x_4423_);
lean_dec(v___x_4422_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4430_; 
v___x_4425_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__8, &l_Int_reduceDvd___redArg___closed__8_once, _init_l_Int_reduceDvd___redArg___closed__8);
v___x_4426_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__11, &l_Int_reduceDvd___redArg___closed__11_once, _init_l_Int_reduceDvd___redArg___closed__11);
v___x_4427_ = l_Lean_eagerReflBoolTrue;
v___x_4428_ = l_Lean_mkApp3(v___x_4426_, v_arg_4384_, v_arg_4381_, v___x_4427_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4428_);
v___x_4430_ = v___x_4420_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; lean_object* v___x_4433_; 
v___x_4431_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4431_, 0, v___x_4425_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
lean_ctor_set_uint8(v___x_4431_, sizeof(void*)*2, v___x_4392_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4431_);
v___x_4433_ = v___x_4411_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4435_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4433_);
v___x_4435_ = v___x_4416_;
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
}
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4444_; 
v___x_4439_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__14, &l_Int_reduceDvd___redArg___closed__14_once, _init_l_Int_reduceDvd___redArg___closed__14);
v___x_4440_ = lean_obj_once(&l_Int_reduceDvd___redArg___closed__17, &l_Int_reduceDvd___redArg___closed__17_once, _init_l_Int_reduceDvd___redArg___closed__17);
v___x_4441_ = l_Lean_eagerReflBoolTrue;
v___x_4442_ = l_Lean_mkApp3(v___x_4440_, v_arg_4384_, v_arg_4381_, v___x_4441_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4442_);
v___x_4444_ = v___x_4420_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4442_);
v___x_4444_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
v___x_4445_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4445_, 0, v___x_4439_);
lean_ctor_set(v___x_4445_, 1, v___x_4444_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*2, v___x_4392_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4445_);
v___x_4447_ = v___x_4411_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4449_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4447_);
v___x_4449_ = v___x_4416_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
}
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_dec(v_a_4414_);
lean_del_object(v___x_4411_);
lean_dec(v_val_4409_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
v___x_4454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4454_);
v___x_4456_ = v___x_4416_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_del_object(v___x_4411_);
lean_dec(v_val_4409_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
v_a_4459_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4413_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4413_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
else
{
lean_object* v___x_4468_; lean_object* v___x_4470_; 
lean_dec(v_a_4405_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
v___x_4468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4468_);
v___x_4470_ = v___x_4407_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
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
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
v_a_4473_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4404_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4404_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
v_a_4482_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4394_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4394_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
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
}
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v_a_4490_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4377_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4377_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
v___jp_4374_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceBinPred___redArg___closed__0));
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___redArg___boxed(lean_object* v_e_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Int_reduceDvd___redArg(v_e_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd(lean_object* v_e_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l_Int_reduceDvd___redArg(v_e_4505_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceDvd___boxed(lean_object* v_e_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Int_reduceDvd(v_e_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4545_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4546_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4543_, v___x_4544_, v___x_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26____boxed(lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_();
return v_res_4548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = lean_alloc_closure((void*)(l_Int_reduceDvd___boxed), 9, 0);
v___x_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_(){
_start:
{
lean_object* v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4553_ = 1;
v___x_4554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_);
v___x_4555_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4552_, v___x_4553_, v___x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28____boxed(lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_();
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_(){
_start:
{
lean_object* v___x_4559_; uint8_t v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceDvd_declare__160___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_26_));
v___x_4560_ = 1;
v___x_4561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_28_);
v___x_4562_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4559_, v___x_4560_, v___x_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30____boxed(lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceDvd___regBuiltin_Int_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_953856760____hygCtx___hyg_30_();
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(lean_object* v_inst_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v___x_4575_; 
v___x_4575_ = l_Lean_Meta_getNatValue_x3f(v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4630_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4578_ = v___x_4575_;
v_isShared_4579_ = v_isSharedCheck_4630_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4630_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
if (lean_obj_tag(v_a_4576_) == 1)
{
lean_object* v_val_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4625_; 
v_val_4580_ = lean_ctor_get(v_a_4576_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v_a_4576_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4582_ = v_a_4576_;
v_isShared_4583_ = v_isSharedCheck_4625_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_val_4580_);
lean_dec(v_a_4576_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4625_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_4568_, v_a_4571_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4616_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4587_ = v___x_4584_;
v_isShared_4588_ = v_isSharedCheck_4616_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4584_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4616_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___y_4590_; lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
v___x_4597_ = l_Lean_Expr_cleanupAnnotations(v_a_4585_);
v___x_4598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___closed__1));
v___x_4599_ = l_Lean_Expr_isConstOf(v___x_4597_, v___x_4598_);
lean_dec_ref(v___x_4597_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
lean_del_object(v___x_4587_);
lean_del_object(v___x_4582_);
lean_dec(v_val_4580_);
v___x_4600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v___x_4600_);
v___x_4602_ = v___x_4578_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
lean_del_object(v___x_4578_);
v___x_4604_ = lean_nat_to_int(v_val_4580_);
v___x_4605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__1);
v___x_4606_ = lean_int_dec_le(v___x_4605_, v___x_4604_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__7);
v___x_4608_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__10);
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__13);
v___x_4610_ = lean_int_neg(v___x_4604_);
lean_dec(v___x_4604_);
v___x_4611_ = l_Int_toNat(v___x_4610_);
lean_dec(v___x_4610_);
v___x_4612_ = l_Lean_instToExprInt_mkNat(v___x_4611_);
v___x_4613_ = l_Lean_mkApp3(v___x_4607_, v___x_4608_, v___x_4609_, v___x_4612_);
v___y_4590_ = v___x_4613_;
goto v___jp_4589_;
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = l_Int_toNat(v___x_4604_);
lean_dec(v___x_4604_);
v___x_4615_ = l_Lean_instToExprInt_mkNat(v___x_4614_);
v___y_4590_ = v___x_4615_;
goto v___jp_4589_;
}
}
v___jp_4589_:
{
lean_object* v___x_4592_; 
if (v_isShared_4583_ == 0)
{
lean_ctor_set_tag(v___x_4582_, 0);
lean_ctor_set(v___x_4582_, 0, v___y_4590_);
v___x_4592_ = v___x_4582_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___y_4590_);
v___x_4592_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4594_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 0, v___x_4592_);
v___x_4594_ = v___x_4587_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_del_object(v___x_4582_);
lean_dec(v_val_4580_);
lean_del_object(v___x_4578_);
v_a_4617_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4584_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4584_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
lean_dec(v_a_4576_);
lean_dec_ref(v_inst_4568_);
v___x_4626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v___x_4626_);
v___x_4628_ = v___x_4578_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4626_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref(v_inst_4568_);
v_a_4631_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4575_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4575_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg___boxed(lean_object* v_inst_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec_ref(v_a_4640_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(lean_object* v_inst_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_inst_4647_, v_a_4648_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___boxed(lean_object* v_inst_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore(v_inst_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg(lean_object* v_e_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4674_, v_a_4676_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___x_4685_ = l_Lean_Expr_cleanupAnnotations(v_a_4684_);
v___x_4686_ = l_Lean_Expr_isApp(v___x_4685_);
if (v___x_4686_ == 0)
{
lean_dec_ref(v___x_4685_);
goto v___jp_4680_;
}
else
{
lean_object* v_arg_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
v_arg_4687_ = lean_ctor_get(v___x_4685_, 1);
lean_inc_ref(v_arg_4687_);
v___x_4688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4685_);
v___x_4689_ = l_Lean_Expr_isApp(v___x_4688_);
if (v___x_4689_ == 0)
{
lean_dec_ref(v___x_4688_);
lean_dec_ref(v_arg_4687_);
goto v___jp_4680_;
}
else
{
lean_object* v_arg_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v_arg_4690_ = lean_ctor_get(v___x_4688_, 1);
lean_inc_ref(v_arg_4690_);
v___x_4691_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4688_);
v___x_4692_ = l_Lean_Expr_isApp(v___x_4691_);
if (v___x_4692_ == 0)
{
lean_dec_ref(v___x_4691_);
lean_dec_ref(v_arg_4690_);
lean_dec_ref(v_arg_4687_);
goto v___jp_4680_;
}
else
{
lean_object* v___x_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v___x_4693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4691_);
v___x_4694_ = ((lean_object*)(l_Int_reduceNatCast___redArg___closed__2));
v___x_4695_ = l_Lean_Expr_isConstOf(v___x_4693_, v___x_4694_);
lean_dec_ref(v___x_4693_);
if (v___x_4695_ == 0)
{
lean_dec_ref(v_arg_4690_);
lean_dec_ref(v_arg_4687_);
goto v___jp_4680_;
}
else
{
lean_object* v___x_4696_; 
v___x_4696_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4690_, v_arg_4687_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
lean_dec_ref(v_arg_4687_);
return v___x_4696_;
}
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
v_a_4697_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4683_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4683_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
v___jp_4680_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4682_, 0, v___x_4681_);
return v___x_4682_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___redArg___boxed(lean_object* v_e_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Int_reduceNatCast___redArg(v_e_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_a_4707_);
lean_dec_ref(v_a_4706_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast(lean_object* v_e_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Int_reduceNatCast___redArg(v_e_4712_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast___boxed(lean_object* v_e_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Int_reduceNatCast(v_e_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4751_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4752_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4749_, v___x_4750_, v___x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23____boxed(lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_();
return v_res_4754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = lean_alloc_closure((void*)(l_Int_reduceNatCast___boxed), 9, 0);
v___x_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4759_ = 1;
v___x_4760_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_);
v___x_4761_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4758_, v___x_4759_, v___x_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25____boxed(lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_();
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4765_; uint8_t v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4766_ = 1;
v___x_4767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_25_);
v___x_4768_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4765_, v___x_4766_, v___x_4767_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27____boxed(lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast___regBuiltin_Int_reduceNatCast_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_27_();
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg(lean_object* v_e_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4775_, v_a_4777_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref_known(v___x_4784_, 1);
v___x_4786_ = l_Lean_Expr_cleanupAnnotations(v_a_4785_);
v___x_4787_ = l_Lean_Expr_isApp(v___x_4786_);
if (v___x_4787_ == 0)
{
lean_dec_ref(v___x_4786_);
goto v___jp_4781_;
}
else
{
lean_object* v_arg_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v_arg_4788_ = lean_ctor_get(v___x_4786_, 1);
lean_inc_ref(v_arg_4788_);
v___x_4789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4786_);
v___x_4790_ = l_Lean_Expr_isApp(v___x_4789_);
if (v___x_4790_ == 0)
{
lean_dec_ref(v___x_4789_);
lean_dec_ref(v_arg_4788_);
goto v___jp_4781_;
}
else
{
lean_object* v_arg_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_arg_4791_ = lean_ctor_get(v___x_4789_, 1);
lean_inc_ref(v_arg_4791_);
v___x_4792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4789_);
v___x_4793_ = l_Lean_Expr_isApp(v___x_4792_);
if (v___x_4793_ == 0)
{
lean_dec_ref(v___x_4792_);
lean_dec_ref(v_arg_4791_);
lean_dec_ref(v_arg_4788_);
goto v___jp_4781_;
}
else
{
lean_object* v___x_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; 
v___x_4794_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4792_);
v___x_4795_ = ((lean_object*)(l_Int_reduceNatCast_x27___redArg___closed__1));
v___x_4796_ = l_Lean_Expr_isConstOf(v___x_4794_, v___x_4795_);
lean_dec_ref(v___x_4794_);
if (v___x_4796_ == 0)
{
lean_dec_ref(v_arg_4791_);
lean_dec_ref(v_arg_4788_);
goto v___jp_4781_;
}
else
{
lean_object* v___x_4797_; 
v___x_4797_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCastCore___redArg(v_arg_4791_, v_arg_4788_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
lean_dec_ref(v_arg_4788_);
return v___x_4797_;
}
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
v_a_4798_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4784_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4784_);
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
v___jp_4781_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceUnary___redArg___closed__0));
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___redArg___boxed(lean_object* v_e_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Int_reduceNatCast_x27___redArg(v_e_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27(lean_object* v_e_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Int_reduceNatCast_x27___redArg(v_e_4813_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Int_reduceNatCast_x27___boxed(lean_object* v_e_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Int_reduceNatCast_x27(v_e_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec(v_a_4824_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_4839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_declare__168___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2728500919____hygCtx___hyg_23_));
v___x_4840_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4841_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4838_, v___x_4839_, v___x_4840_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23____boxed(lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_();
return v_res_4843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = lean_alloc_closure((void*)(l_Int_reduceNatCast_x27___boxed), 9, 0);
v___x_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_4847_; uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_4848_ = 1;
v___x_4849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_);
v___x_4850_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4847_, v___x_4848_, v___x_4849_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25____boxed(lean_object* v_a_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_();
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_4854_; uint8_t v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNatCast_x27_declare__173___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_23_));
v___x_4855_ = 1;
v___x_4856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_25_);
v___x_4857_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4854_, v___x_4855_, v___x_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27____boxed(lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNatCast_x27___regBuiltin_Int_reduceNatCast_x27_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2649888432____hygCtx___hyg_27_();
return v_res_4859_;
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
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0____regBuiltin_Int_reduceNeg_declare__27_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_0__Int_reduceNeg___regBuiltin_Int_reduceNeg_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int_2628830623____hygCtx___hyg_29_();
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
