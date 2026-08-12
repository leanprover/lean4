// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Int.Basic import Lean.OrderLevel
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "norm_eq_var_const"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 3, 128, 209, 83, 119, 41, 246)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_eq_false_of_divCoeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(166, 111, 217, 210, 57, 89, 97, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_eq_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(160, 202, 127, 206, 181, 96, 119, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(97, 114, 204, 9, 138, 244, 137, 99)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "norm_eq_var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(18, 165, 157, 183, 182, 21, 11, 103)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(203, 67, 11, 240, 218, 30, 121, 196)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(246, 204, 242, 159, 237, 232, 61, 227)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_le_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 37, 231, 141, 181, 61, 212, 111)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "norm_le_coeff_tight"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 84, 17, 148, 219, 118, 189, 43)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 21, 225, 1, 193, 118, 239, 219)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(157, 27, 219, 76, 37, 196, 87, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(65, 108, 55, 118, 18, 74, 38, 151)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_ge_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(87, 141, 152, 40, 61, 44, 151, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_lt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(214, 41, 233, 126, 147, 68, 29, 47)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_gt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 48, 12, 204, 229, 102, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "norm_dvd_gcd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 232, 181, 248, 19, 12, 233, 169)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "norm_dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(131, 13, 167, 71, 102, 170, 234, 147)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dvd_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 145, 10, 79, 196, 12, 17, 141)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_of_norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 40, 229, 149, 41, 35, 142, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(lean_object* v_k_1_, lean_object* v_p_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_dec_eq(v_k_1_, v___x_3_);
if (v___x_4_ == 0)
{
if (lean_obj_tag(v_p_2_) == 0)
{
lean_object* v_k_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_k_5_ = lean_ctor_get(v_p_2_, 0);
v___x_6_ = lean_nat_abs(v_k_5_);
v___x_7_ = lean_nat_gcd(v_k_1_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v_k_1_);
return v___x_7_;
}
else
{
lean_object* v_k_8_; lean_object* v_p_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_k_8_ = lean_ctor_get(v_p_2_, 0);
v_p_9_ = lean_ctor_get(v_p_2_, 2);
v___x_10_ = lean_nat_abs(v_k_8_);
v___x_11_ = lean_nat_gcd(v_k_1_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v_k_1_);
v_k_1_ = v___x_11_;
v_p_2_ = v_p_9_;
goto _start;
}
}
else
{
return v_k_1_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go___boxed(lean_object* v_k_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(v_k_13_, v_p_14_);
lean_dec_ref(v_p_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll(lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v_k_17_; lean_object* v___x_18_; 
v_k_17_ = lean_ctor_get(v_x_16_, 0);
v___x_18_ = lean_nat_abs(v_k_17_);
return v___x_18_;
}
else
{
lean_object* v_k_19_; lean_object* v_p_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_k_19_ = lean_ctor_get(v_x_16_, 0);
v_p_20_ = lean_ctor_get(v_x_16_, 2);
v___x_21_ = lean_nat_abs(v_k_19_);
v___x_22_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(v___x_21_, v_p_20_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll___boxed(lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Int_Internal_Linear_Poly_gcdAll(v_x_23_);
lean_dec_ref(v_x_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(lean_object* v_k_25_, lean_object* v_p_26_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_dec_eq(v_k_25_, v___x_27_);
if (v___x_28_ == 0)
{
if (lean_obj_tag(v_p_26_) == 0)
{
return v_k_25_;
}
else
{
lean_object* v_k_29_; lean_object* v_p_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_k_29_ = lean_ctor_get(v_p_26_, 0);
v_p_30_ = lean_ctor_get(v_p_26_, 2);
v___x_31_ = lean_nat_abs(v_k_29_);
v___x_32_ = lean_nat_gcd(v_k_25_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v_k_25_);
v_k_25_ = v___x_32_;
v_p_26_ = v_p_30_;
goto _start;
}
}
else
{
return v_k_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* v_k_34_, lean_object* v_p_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(v_k_34_, v_p_35_);
lean_dec_ref(v_p_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27(lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_unsigned_to_nat(1u);
return v___x_38_;
}
else
{
lean_object* v_k_39_; lean_object* v_p_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_k_39_ = lean_ctor_get(v_x_37_, 0);
v_p_40_ = lean_ctor_get(v_x_37_, 2);
v___x_41_ = lean_nat_abs(v_k_39_);
v___x_42_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(v___x_41_, v_p_40_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object* v_a_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_nat_to_int(v_a_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object* v___x_47_, lean_object* v_snd_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_array_get_borrowed(v___x_47_, v_snd_48_, v_x_49_);
lean_inc(v___x_50_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object* v___x_51_, lean_object* v_snd_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(v___x_51_, v_snd_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec_ref(v_snd_52_);
lean_dec_ref(v___x_51_);
return v_res_54_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4));
v___x_66_ = l_Lean_mkConst(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8));
v___x_74_ = l_Lean_mkConst(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_box(0);
v___x_82_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11));
v___x_83_ = l_Lean_mkConst(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Lean_Level_ofNat(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_95_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15));
v___x_96_ = l_Lean_Expr_const___override(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_box(0);
v___x_100_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_101_ = l_Lean_Expr_const___override(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_box(0);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22));
v___x_108_ = l_Lean_Expr_const___override(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_110_ = l_Lean_mkIntLit(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29));
v___x_128_ = l_Lean_mkConst(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_132_ = lean_int_neg(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34));
v___x_141_ = l_Lean_mkConst(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38));
v___x_149_ = l_Lean_mkConst(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41));
v___x_158_ = l_Lean_mkConst(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44));
v___x_167_ = l_Lean_mkConst(v___x_166_, v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_555_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_555_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_555_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_555_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
if (lean_obj_tag(v_a_175_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_550_; 
v_val_179_ = lean_ctor_get(v_a_175_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_175_);
if (v_isSharedCheck_550_ == 0)
{
v___x_181_ = v_a_175_;
v_isShared_182_ = v_isSharedCheck_550_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v_a_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_550_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_snd_183_; lean_object* v_fst_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_549_; 
v_snd_183_ = lean_ctor_get(v_val_179_, 1);
v_fst_184_ = lean_ctor_get(v_val_179_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_val_179_);
if (v_isSharedCheck_549_ == 0)
{
v___x_186_ = v_val_179_;
v_isShared_187_ = v_isSharedCheck_549_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snd_183_);
lean_inc(v_fst_184_);
lean_dec(v_val_179_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_549_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_548_; 
v_fst_188_ = lean_ctor_get(v_snd_183_, 0);
v_snd_189_ = lean_ctor_get(v_snd_183_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_snd_183_);
if (v_isSharedCheck_548_ == 0)
{
v___x_191_ = v_snd_183_;
v_isShared_192_ = v_isSharedCheck_548_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_snd_189_);
lean_inc(v_fst_188_);
lean_dec(v_snd_183_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_548_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_189_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_194_, 0, v___x_193_);
lean_closure_set(v___f_194_, 1, v_snd_189_);
lean_inc(v_fst_184_);
lean_inc_ref(v___f_194_);
v___x_195_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_184_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_539_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_539_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_539_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_539_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; 
lean_inc(v_fst_188_);
lean_inc_ref(v___f_194_);
v___x_200_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_188_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_530_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_530_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_530_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_530_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; uint8_t v___y_398_; uint8_t v___x_470_; 
v___x_205_ = l_Lean_mkIntEq(v_a_196_, v_a_201_);
lean_inc(v_fst_188_);
lean_inc(v_fst_184_);
v___x_282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_282_, 0, v_fst_184_);
lean_ctor_set(v___x_282_, 1, v_fst_188_);
v___x_283_ = l_Int_Internal_Linear_Expr_norm(v___x_282_);
lean_dec_ref_known(v___x_282_, 2);
v___x_470_ = l_Int_Internal_Linear_Poly_isUnsatEq(v___x_283_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = l_Int_Internal_Linear_Poly_isValidEq(v___x_283_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
lean_inc_ref(v___x_283_);
v___x_472_ = l_Int_Internal_Linear_Poly_toExpr(v___x_283_);
v___x_473_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_472_, v_fst_184_);
lean_dec_ref(v___x_472_);
if (v___x_473_ == 0)
{
v___y_398_ = v___x_473_;
goto v___jp_397_;
}
else
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_475_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_188_, v___x_474_);
v___y_398_ = v___x_475_;
goto v___jp_397_;
}
}
else
{
lean_object* v___x_476_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v___x_476_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_494_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_494_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_494_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_494_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_481_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_482_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42);
v___x_483_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_484_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_485_ = l_Lean_eagerReflBoolTrue;
v___x_486_ = l_Lean_mkApp4(v___x_482_, v_a_477_, v___x_483_, v___x_484_, v___x_485_);
v___x_487_ = l_Lean_mkPropEq(v___x_205_, v___x_481_);
v___x_488_ = l_Lean_Meta_mkExpectedPropHint(v___x_486_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_481_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_490_);
v___x_492_ = v___x_479_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_495_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_476_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_476_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v___x_503_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_521_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_521_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_521_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_521_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_508_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_509_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45);
v___x_510_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_511_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_512_ = l_Lean_eagerReflBoolTrue;
v___x_513_ = l_Lean_mkApp4(v___x_509_, v_a_504_, v___x_510_, v___x_511_, v___x_512_);
v___x_514_ = l_Lean_mkPropEq(v___x_205_, v___x_508_);
v___x_515_ = l_Lean_Meta_mkExpectedPropHint(v___x_513_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_508_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_517_);
v___x_519_ = v___x_506_;
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
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_522_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_503_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_503_);
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
v___jp_206_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_213_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_207_);
v___x_214_ = l_Lean_mkApp5(v___y_207_, v___y_211_, v___y_210_, v___y_209_, v___y_212_, v___x_213_);
lean_inc_ref_n(v___y_208_, 2);
v___x_215_ = l_Lean_mkPropEq(v___x_205_, v___y_208_);
v___x_216_ = l_Lean_Meta_mkExpectedPropHint(v___x_214_, v___x_215_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_216_);
lean_ctor_set(v___x_191_, 0, v___y_208_);
v___x_218_ = v___x_191_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___y_208_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_218_);
v___x_220_ = v___x_181_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_220_);
v___x_222_ = v___x_203_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
v___jp_226_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_234_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_229_);
v___x_235_ = l_Lean_mkApp6(v___y_229_, v___y_230_, v___y_227_, v___y_232_, v___y_231_, v___y_233_, v___x_234_);
lean_inc_ref(v___y_228_);
v___x_236_ = l_Lean_mkPropEq(v___x_205_, v___y_228_);
v___x_237_ = l_Lean_Meta_mkExpectedPropHint(v___x_235_, v___x_236_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_237_);
lean_ctor_set(v___x_186_, 0, v___y_228_);
v___x_239_ = v___x_186_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___y_228_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_240_);
v___x_242_ = v___x_198_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
v___jp_245_:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
lean_inc_ref(v___y_248_);
v___x_249_ = l_Lean_mkIntEq(v___y_247_, v___y_248_);
v___x_250_ = lean_expr_eqv(v___x_249_, v___x_205_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_del_object(v___x_177_);
v___x_251_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_269_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_269_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_257_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_258_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_259_ = l_Lean_mkNatLit(v___y_246_);
v___x_260_ = l_Lean_eagerReflBoolTrue;
v___x_261_ = l_Lean_mkApp6(v___x_256_, v_a_252_, v___x_257_, v___x_258_, v___x_259_, v___y_248_, v___x_260_);
lean_inc_ref(v___x_249_);
v___x_262_ = l_Lean_mkPropEq(v___x_205_, v___x_249_);
v___x_263_ = l_Lean_Meta_mkExpectedPropHint(v___x_261_, v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_249_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_265_);
v___x_267_ = v___x_254_;
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
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v___x_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_246_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_270_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_251_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_251_);
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
lean_dec_ref(v___x_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_246_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v___x_278_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_278_);
v___x_280_ = v___x_177_;
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
v___jp_284_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___x_283_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_292_ = l_Int_Internal_Linear_Poly_getConst(v___x_283_);
v___x_293_ = lean_nat_to_int(v___x_289_);
v___x_294_ = lean_int_emod(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_296_ = lean_int_dec_eq(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_186_);
v___x_297_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_300_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12);
v___x_301_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_302_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_303_ = lean_int_dec_le(v___x_295_, v___x_293_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_304_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_305_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_306_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_307_ = lean_int_neg(v___x_293_);
lean_dec(v___x_293_);
v___x_308_ = l_Int_toNat(v___x_307_);
lean_dec(v___x_307_);
v___x_309_ = l_Lean_instToExprInt_mkNat(v___x_308_);
v___x_310_ = l_Lean_mkApp3(v___x_304_, v___x_305_, v___x_306_, v___x_309_);
v___y_207_ = v___x_300_;
v___y_208_ = v___x_299_;
v___y_209_ = v___x_302_;
v___y_210_ = v___x_301_;
v___y_211_ = v_a_298_;
v___y_212_ = v___x_310_;
goto v___jp_206_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Int_toNat(v___x_293_);
lean_dec(v___x_293_);
v___x_312_ = l_Lean_instToExprInt_mkNat(v___x_311_);
v___y_207_ = v___x_300_;
v___y_208_ = v___x_299_;
v___y_209_ = v___x_302_;
v___y_210_ = v___x_301_;
v___y_211_ = v_a_298_;
v___y_212_ = v___x_312_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_203_);
lean_del_object(v___x_191_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
v_a_313_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_297_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_297_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_203_);
lean_del_object(v___x_191_);
lean_del_object(v___x_181_);
v___x_321_ = l_Int_Internal_Linear_Poly_div(v___x_293_, v___x_283_);
lean_inc_ref(v___x_321_);
v___x_322_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_327_ = l_Lean_mkIntEq(v_a_323_, v___x_326_);
v___x_328_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27);
v___x_329_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_330_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_331_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_321_);
v___x_332_ = lean_int_dec_le(v___x_295_, v___x_293_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_333_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_334_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_335_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_336_ = lean_int_neg(v___x_293_);
lean_dec(v___x_293_);
v___x_337_ = l_Int_toNat(v___x_336_);
lean_dec(v___x_336_);
v___x_338_ = l_Lean_instToExprInt_mkNat(v___x_337_);
v___x_339_ = l_Lean_mkApp3(v___x_333_, v___x_334_, v___x_335_, v___x_338_);
v___y_227_ = v___x_329_;
v___y_228_ = v___x_327_;
v___y_229_ = v___x_328_;
v___y_230_ = v_a_325_;
v___y_231_ = v___x_331_;
v___y_232_ = v___x_330_;
v___y_233_ = v___x_339_;
goto v___jp_226_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Int_toNat(v___x_293_);
lean_dec(v___x_293_);
v___x_341_ = l_Lean_instToExprInt_mkNat(v___x_340_);
v___y_227_ = v___x_329_;
v___y_228_ = v___x_327_;
v___y_229_ = v___x_328_;
v___y_230_ = v_a_325_;
v___y_231_ = v___x_331_;
v___y_232_ = v___x_330_;
v___y_233_ = v___x_341_;
goto v___jp_226_;
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_323_);
lean_dec_ref(v___x_321_);
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
v_a_342_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_324_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_324_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v___x_321_);
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
v_a_350_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_322_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_322_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v___x_289_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
lean_inc_ref(v___x_283_);
v___x_358_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_283_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_380_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_380_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_380_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_380_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_365_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_366_ = l_Lean_mkIntEq(v_a_359_, v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_368_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_369_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_370_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_283_);
v___x_371_ = l_Lean_eagerReflBoolTrue;
v___x_372_ = l_Lean_mkApp5(v___x_367_, v_a_361_, v___x_368_, v___x_369_, v___x_370_, v___x_371_);
lean_inc_ref(v___x_366_);
v___x_373_ = l_Lean_mkPropEq(v___x_205_, v___x_366_);
v___x_374_ = l_Lean_Meta_mkExpectedPropHint(v___x_372_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_366_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_376_);
v___x_378_ = v___x_363_;
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
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_a_359_);
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_381_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_360_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_360_);
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
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_389_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_358_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_358_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
v___jp_397_:
{
if (v___y_398_ == 0)
{
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_k_399_; lean_object* v_v_400_; lean_object* v_p_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_k_399_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_k_399_);
v_v_400_ = lean_ctor_get(v___x_283_, 1);
lean_inc(v_v_400_);
v_p_401_ = lean_ctor_get(v___x_283_, 2);
lean_inc_ref(v_p_401_);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_403_ = lean_int_dec_eq(v_k_399_, v___x_402_);
lean_dec(v_k_399_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_p_401_);
lean_dec(v_v_400_);
lean_del_object(v___x_177_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
if (lean_obj_tag(v_p_401_) == 0)
{
lean_object* v_k_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
lean_dec_ref_known(v___x_283_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
v_k_404_ = lean_ctor_get(v_p_401_, 0);
lean_inc(v_k_404_);
lean_dec_ref_known(v_p_401_, 1);
v___x_405_ = lean_array_get_borrowed(v___x_193_, v_snd_189_, v_v_400_);
v___x_406_ = lean_int_neg(v_k_404_);
lean_dec(v_k_404_);
v___x_407_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_408_ = lean_int_dec_le(v___x_407_, v___x_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_409_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_410_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_412_ = lean_int_neg(v___x_406_);
lean_dec(v___x_406_);
v___x_413_ = l_Int_toNat(v___x_412_);
lean_dec(v___x_412_);
v___x_414_ = l_Lean_instToExprInt_mkNat(v___x_413_);
v___x_415_ = l_Lean_mkApp3(v___x_409_, v___x_410_, v___x_411_, v___x_414_);
lean_inc(v___x_405_);
v___y_246_ = v_v_400_;
v___y_247_ = v___x_405_;
v___y_248_ = v___x_415_;
goto v___jp_245_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = l_Int_toNat(v___x_406_);
lean_dec(v___x_406_);
v___x_417_ = l_Lean_instToExprInt_mkNat(v___x_416_);
lean_inc(v___x_405_);
v___y_246_ = v_v_400_;
v___y_247_ = v___x_405_;
v___y_248_ = v___x_417_;
goto v___jp_245_;
}
}
else
{
lean_object* v_k_418_; lean_object* v_v_419_; lean_object* v_p_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
lean_del_object(v___x_177_);
v_k_418_ = lean_ctor_get(v_p_401_, 0);
lean_inc(v_k_418_);
v_v_419_ = lean_ctor_get(v_p_401_, 1);
lean_inc(v_v_419_);
v_p_420_ = lean_ctor_get(v_p_401_, 2);
lean_inc_ref(v_p_420_);
lean_dec_ref_known(v_p_401_, 3);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32);
v___x_422_ = lean_int_dec_eq(v_k_418_, v___x_421_);
lean_dec(v_k_418_);
if (v___x_422_ == 0)
{
lean_dec_ref(v_p_420_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
if (lean_obj_tag(v_p_420_) == 0)
{
lean_object* v_k_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_467_; 
v_k_423_ = lean_ctor_get(v_p_420_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_p_420_);
if (v_isSharedCheck_467_ == 0)
{
v___x_425_ = v_p_420_;
v_isShared_426_ = v_isSharedCheck_467_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_k_423_);
lean_dec(v_p_420_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_467_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_428_ = lean_int_dec_eq(v_k_423_, v___x_427_);
lean_dec(v_k_423_);
if (v___x_428_ == 0)
{
lean_del_object(v___x_425_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
lean_dec_ref_known(v___x_283_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
v___x_429_ = lean_array_get_borrowed(v___x_193_, v_snd_189_, v_v_400_);
v___x_430_ = lean_array_get_borrowed(v___x_193_, v_snd_189_, v_v_419_);
lean_inc(v___x_430_);
lean_inc(v___x_429_);
v___x_431_ = l_Lean_mkIntEq(v___x_429_, v___x_430_);
v___x_432_ = lean_expr_eqv(v___x_431_, v___x_205_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_454_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_454_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_454_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_454_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_438_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
v___x_439_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_440_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_441_ = l_Lean_mkNatLit(v_v_400_);
v___x_442_ = l_Lean_mkNatLit(v_v_419_);
v___x_443_ = l_Lean_eagerReflBoolTrue;
v___x_444_ = l_Lean_mkApp6(v___x_438_, v_a_434_, v___x_439_, v___x_440_, v___x_441_, v___x_442_, v___x_443_);
lean_inc_ref(v___x_431_);
v___x_445_ = l_Lean_mkPropEq(v___x_205_, v___x_431_);
v___x_446_ = l_Lean_Meta_mkExpectedPropHint(v___x_444_, v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_431_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 1);
lean_ctor_set(v___x_425_, 0, v___x_447_);
v___x_449_ = v___x_425_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_449_);
v___x_451_ = v___x_436_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v___x_431_);
lean_del_object(v___x_425_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_455_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_433_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_433_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec_ref(v___x_431_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v___x_463_ = lean_box(0);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_463_);
v___x_465_ = v___x_425_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_420_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
}
}
}
}
else
{
lean_del_object(v___x_177_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_198_);
lean_dec(v_a_196_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v_a_531_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_200_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_200_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v_a_540_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_195_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_195_);
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
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_a_175_);
v___x_551_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_551_);
v___x_553_ = v___x_177_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_174_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_174_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(v_e_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_box(0);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
v___x_579_ = l_Lean_mkConst(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
v___x_588_ = l_Lean_mkConst(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
v___x_597_ = l_Lean_mkConst(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
v___x_606_ = l_Lean_mkConst(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_box(0);
v___x_614_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
v___x_615_ = l_Lean_mkConst(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = l_Lean_Level_ofNat(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* v_e_623_, uint8_t v_checkIfModified_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v_h_633_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; uint8_t v___y_676_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v_leLvl_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___x_909_; uint8_t v___y_911_; lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_909_ = l_Lean_instInhabitedExpr;
v___x_949_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18));
v___x_950_ = l_Lean_Expr_isAppOf(v_e_623_, v___x_949_);
if (v___x_950_ == 0)
{
v___y_911_ = v___x_950_;
goto v___jp_910_;
}
else
{
v___y_911_ = v_checkIfModified_624_;
goto v___jp_910_;
}
v___jp_630_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_inc_ref(v___y_632_);
v___x_634_ = l_Lean_mkPropEq(v___y_631_, v___y_632_);
v___x_635_ = l_Lean_Meta_mkExpectedPropHint(v_h_633_, v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_632_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
v___jp_639_:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_646_);
v___x_649_ = l_Lean_mkApp6(v___y_646_, v___y_642_, v___y_644_, v___y_640_, v___y_641_, v___y_647_, v___x_648_);
v___y_631_ = v___y_643_;
v___y_632_ = v___y_645_;
v_h_633_ = v___x_649_;
goto v___jp_630_;
}
v___jp_650_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_651_);
v___x_660_ = l_Lean_mkApp6(v___y_651_, v___y_652_, v___y_656_, v___y_657_, v___y_654_, v___y_658_, v___x_659_);
v___y_631_ = v___y_653_;
v___y_632_ = v___y_655_;
v_h_633_ = v___x_660_;
goto v___jp_630_;
}
v___jp_661_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = l_Int_Internal_Linear_Poly_div(v___y_666_, v___y_664_);
lean_inc_ref(v___x_677_);
v___x_678_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_668_, v___x_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_680_ = l_Lean_mkIntLit(v___y_674_);
lean_inc(v___y_665_);
v___x_681_ = l_Lean_mkIntLE(v___y_665_, v_a_679_, v___x_680_);
if (v___y_676_ == 0)
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_662_, v___y_672_, v___y_663_, v___y_667_, v___y_673_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_box(0);
v___x_685_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
v___x_686_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_675_);
v___x_687_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_669_);
v___x_688_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_677_);
v___x_689_ = lean_int_dec_le(v___y_674_, v___y_666_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_690_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15));
v___x_691_ = l_Lean_Level_ofNat(v___y_671_);
v___x_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_684_);
v___x_693_ = l_Lean_Expr_const___override(v___x_690_, v___x_692_);
v___x_694_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_695_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_696_ = lean_int_neg(v___y_666_);
lean_dec(v___y_666_);
v___x_697_ = l_Int_toNat(v___x_696_);
lean_dec(v___x_696_);
v___x_698_ = l_Lean_instToExprInt_mkNat(v___x_697_);
v___x_699_ = l_Lean_mkApp3(v___x_693_, v___x_694_, v___x_695_, v___x_698_);
v___y_651_ = v___x_685_;
v___y_652_ = v_a_683_;
v___y_653_ = v___y_670_;
v___y_654_ = v___x_688_;
v___y_655_ = v___x_681_;
v___y_656_ = v___x_686_;
v___y_657_ = v___x_687_;
v___y_658_ = v___x_699_;
goto v___jp_650_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = l_Int_toNat(v___y_666_);
lean_dec(v___y_666_);
v___x_701_ = l_Lean_instToExprInt_mkNat(v___x_700_);
v___y_651_ = v___x_685_;
v___y_652_ = v_a_683_;
v___y_653_ = v___y_670_;
v___y_654_ = v___x_688_;
v___y_655_ = v___x_681_;
v___y_656_ = v___x_686_;
v___y_657_ = v___x_687_;
v___y_658_ = v___x_701_;
goto v___jp_650_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_666_);
v_a_702_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_682_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_682_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_662_, v___y_672_, v___y_663_, v___y_667_, v___y_673_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_box(0);
v___x_713_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
v___x_714_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_675_);
v___x_715_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_669_);
v___x_716_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_677_);
v___x_717_ = lean_int_dec_le(v___y_674_, v___y_666_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_718_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15));
v___x_719_ = l_Lean_Level_ofNat(v___y_671_);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_712_);
v___x_721_ = l_Lean_Expr_const___override(v___x_718_, v___x_720_);
v___x_722_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_723_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_724_ = lean_int_neg(v___y_666_);
lean_dec(v___y_666_);
v___x_725_ = l_Int_toNat(v___x_724_);
lean_dec(v___x_724_);
v___x_726_ = l_Lean_instToExprInt_mkNat(v___x_725_);
v___x_727_ = l_Lean_mkApp3(v___x_721_, v___x_722_, v___x_723_, v___x_726_);
v___y_640_ = v___x_715_;
v___y_641_ = v___x_716_;
v___y_642_ = v_a_711_;
v___y_643_ = v___y_670_;
v___y_644_ = v___x_714_;
v___y_645_ = v___x_681_;
v___y_646_ = v___x_713_;
v___y_647_ = v___x_727_;
goto v___jp_639_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = l_Int_toNat(v___y_666_);
lean_dec(v___y_666_);
v___x_729_ = l_Lean_instToExprInt_mkNat(v___x_728_);
v___y_640_ = v___x_715_;
v___y_641_ = v___x_716_;
v___y_642_ = v_a_711_;
v___y_643_ = v___y_670_;
v___y_644_ = v___x_714_;
v___y_645_ = v___x_681_;
v___y_646_ = v___x_713_;
v___y_647_ = v___x_729_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___x_681_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_666_);
v_a_730_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_710_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_710_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_677_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_662_);
v_a_738_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_678_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_678_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
v___jp_746_:
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___y_751_);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_dec_eq(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_761_ = l_Int_Internal_Linear_Poly_getConst(v___y_751_);
v___x_762_ = lean_nat_to_int(v___x_758_);
v___x_763_ = lean_int_emod(v___x_761_, v___x_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_766_ = lean_int_dec_eq(v___x_763_, v___x_765_);
lean_dec(v___x_763_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
v___x_767_ = 1;
v___y_662_ = v___y_748_;
v___y_663_ = v___y_747_;
v___y_664_ = v___y_751_;
v___y_665_ = v___y_755_;
v___y_666_ = v___x_762_;
v___y_667_ = v___y_756_;
v___y_668_ = v___y_749_;
v___y_669_ = v___y_750_;
v___y_670_ = v___y_752_;
v___y_671_ = v___x_764_;
v___y_672_ = v___y_754_;
v___y_673_ = v___y_753_;
v___y_674_ = v___x_765_;
v___y_675_ = v___y_757_;
v___y_676_ = v___x_767_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___y_748_;
v___y_663_ = v___y_747_;
v___y_664_ = v___y_751_;
v___y_665_ = v___y_755_;
v___y_666_ = v___x_762_;
v___y_667_ = v___y_756_;
v___y_668_ = v___y_749_;
v___y_669_ = v___y_750_;
v___y_670_ = v___y_752_;
v___y_671_ = v___x_764_;
v___y_672_ = v___y_754_;
v___y_673_ = v___y_753_;
v___y_674_ = v___x_765_;
v___y_675_ = v___y_757_;
v___y_676_ = v___x_760_;
goto v___jp_661_;
}
}
else
{
lean_object* v___x_768_; 
lean_dec(v___x_758_);
lean_inc_ref(v___y_751_);
v___x_768_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_749_, v___y_751_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_748_, v___y_754_, v___y_747_, v___y_756_, v___y_753_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_790_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_790_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_790_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_790_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_775_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
lean_inc(v___y_755_);
v___x_776_ = l_Lean_mkIntLE(v___y_755_, v_a_769_, v___x_775_);
v___x_777_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
v___x_778_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_757_);
v___x_779_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_750_);
v___x_780_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_751_);
v___x_781_ = l_Lean_eagerReflBoolTrue;
v___x_782_ = l_Lean_mkApp5(v___x_777_, v_a_771_, v___x_778_, v___x_779_, v___x_780_, v___x_781_);
lean_inc_ref(v___x_776_);
v___x_783_ = l_Lean_mkPropEq(v___y_752_, v___x_776_);
v___x_784_ = l_Lean_Meta_mkExpectedPropHint(v___x_782_, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_776_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_786_);
v___x_788_ = v___x_773_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_769_);
lean_dec_ref(v___y_757_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v___y_750_);
v_a_791_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_770_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_770_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___y_757_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec_ref(v___y_748_);
v_a_799_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_768_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_768_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
v___jp_807_:
{
lean_object* v___x_818_; 
lean_inc_ref(v___y_812_);
lean_inc_ref(v___y_809_);
v___x_818_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___y_809_, v___y_812_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
lean_inc_ref(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_820_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_892_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_892_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_892_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_892_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
lean_inc(v_leLvl_813_);
v___x_825_ = l_Lean_mkIntLE(v_leLvl_813_, v_a_819_, v_a_821_);
lean_inc_ref(v___y_810_);
lean_inc_ref(v___y_812_);
v___x_826_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_826_, 0, v___y_812_);
lean_ctor_set(v___x_826_, 1, v___y_810_);
v___x_827_ = l_Int_Internal_Linear_Expr_norm(v___x_826_);
lean_dec_ref_known(v___x_826_, 2);
v___x_828_ = l_Int_Internal_Linear_Poly_isUnsatLe(v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = l_Int_Internal_Linear_Poly_isValidLe(v___x_827_);
if (v___x_829_ == 0)
{
if (v___y_811_ == 0)
{
lean_del_object(v___x_823_);
v___y_747_ = v___y_815_;
v___y_748_ = v___y_808_;
v___y_749_ = v___y_809_;
v___y_750_ = v___y_810_;
v___y_751_ = v___x_827_;
v___y_752_ = v___x_825_;
v___y_753_ = v___y_817_;
v___y_754_ = v___y_814_;
v___y_755_ = v_leLvl_813_;
v___y_756_ = v___y_816_;
v___y_757_ = v___y_812_;
goto v___jp_746_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
lean_inc_ref(v___x_827_);
v___x_830_ = l_Int_Internal_Linear_Poly_toExpr(v___x_827_);
v___x_831_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_830_, v___y_812_);
lean_dec_ref(v___x_830_);
if (v___x_831_ == 0)
{
lean_del_object(v___x_823_);
v___y_747_ = v___y_815_;
v___y_748_ = v___y_808_;
v___y_749_ = v___y_809_;
v___y_750_ = v___y_810_;
v___y_751_ = v___x_827_;
v___y_752_ = v___x_825_;
v___y_753_ = v___y_817_;
v___y_754_ = v___y_814_;
v___y_755_ = v_leLvl_813_;
v___y_756_ = v___y_816_;
v___y_757_ = v___y_812_;
goto v___jp_746_;
}
else
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_833_ = l_Int_Internal_Linear_instBEqExpr_beq(v___y_810_, v___x_832_);
if (v___x_833_ == 0)
{
lean_del_object(v___x_823_);
v___y_747_ = v___y_815_;
v___y_748_ = v___y_808_;
v___y_749_ = v___y_809_;
v___y_750_ = v___y_810_;
v___y_751_ = v___x_827_;
v___y_752_ = v___x_825_;
v___y_753_ = v___y_817_;
v___y_754_ = v___y_814_;
v___y_755_ = v_leLvl_813_;
v___y_756_ = v___y_816_;
v___y_757_ = v___y_812_;
goto v___jp_746_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec_ref(v___x_827_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
v___x_834_ = lean_box(0);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_834_);
v___x_836_ = v___x_823_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec_ref(v___x_827_);
lean_del_object(v___x_823_);
lean_dec_ref(v___y_809_);
v___x_838_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_808_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_856_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_856_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_856_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_856_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_843_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_844_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
v___x_845_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_812_);
v___x_846_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_810_);
v___x_847_ = l_Lean_eagerReflBoolTrue;
v___x_848_ = l_Lean_mkApp4(v___x_844_, v_a_839_, v___x_845_, v___x_846_, v___x_847_);
v___x_849_ = l_Lean_mkPropEq(v___x_825_, v___x_843_);
v___x_850_ = l_Lean_Meta_mkExpectedPropHint(v___x_848_, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_843_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_852_);
v___x_854_ = v___x_841_;
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
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___x_825_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_810_);
v_a_857_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_838_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_838_);
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
}
else
{
lean_object* v___x_865_; 
lean_dec_ref(v___x_827_);
lean_del_object(v___x_823_);
lean_dec_ref(v___y_809_);
v___x_865_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_808_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_883_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_883_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_883_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_883_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_870_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_871_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
v___x_872_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_812_);
v___x_873_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_810_);
v___x_874_ = l_Lean_eagerReflBoolTrue;
v___x_875_ = l_Lean_mkApp4(v___x_871_, v_a_866_, v___x_872_, v___x_873_, v___x_874_);
v___x_876_ = l_Lean_mkPropEq(v___x_825_, v___x_870_);
v___x_877_ = l_Lean_Meta_mkExpectedPropHint(v___x_875_, v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_870_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_879_);
v___x_881_ = v___x_868_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___x_825_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_810_);
v_a_884_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_865_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_865_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_a_819_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
v_a_893_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_820_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_820_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
v_a_901_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_818_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_818_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
v___jp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_940_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_940_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_940_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_940_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
if (lean_obj_tag(v_a_913_) == 1)
{
lean_object* v_val_917_; lean_object* v_snd_918_; lean_object* v_fst_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_922_; 
lean_del_object(v___x_915_);
v_val_917_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_val_917_);
lean_dec_ref_known(v_a_913_, 1);
v_snd_918_ = lean_ctor_get(v_val_917_, 1);
lean_inc(v_snd_918_);
v_fst_919_ = lean_ctor_get(v_val_917_, 0);
lean_inc(v_fst_919_);
lean_dec(v_val_917_);
v_fst_920_ = lean_ctor_get(v_snd_918_, 0);
lean_inc(v_fst_920_);
v_snd_921_ = lean_ctor_get(v_snd_918_, 1);
lean_inc(v_snd_921_);
lean_dec(v_snd_918_);
v___x_922_ = l_Lean_leCarrierIsSort(v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___f_924_; uint8_t v___x_925_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
lean_inc(v_snd_921_);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_924_, 0, v___x_909_);
lean_closure_set(v___f_924_, 1, v_snd_921_);
v___x_925_ = lean_unbox(v_a_923_);
lean_dec(v_a_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
v___x_926_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
v___y_808_ = v_snd_921_;
v___y_809_ = v___f_924_;
v___y_810_ = v_fst_920_;
v___y_811_ = v___y_911_;
v___y_812_ = v_fst_919_;
v_leLvl_813_ = v___x_926_;
v___y_814_ = v_a_625_;
v___y_815_ = v_a_626_;
v___y_816_ = v_a_627_;
v___y_817_ = v_a_628_;
goto v___jp_807_;
}
else
{
lean_object* v___x_927_; 
v___x_927_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15);
v___y_808_ = v_snd_921_;
v___y_809_ = v___f_924_;
v___y_810_ = v_fst_920_;
v___y_811_ = v___y_911_;
v___y_812_ = v_fst_919_;
v_leLvl_813_ = v___x_927_;
v___y_814_ = v_a_625_;
v___y_815_ = v_a_626_;
v___y_816_ = v_a_627_;
v___y_817_ = v_a_628_;
goto v___jp_807_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_snd_921_);
lean_dec(v_fst_920_);
lean_dec(v_fst_919_);
v_a_928_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_922_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_922_);
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
lean_dec(v_a_913_);
v___x_936_ = lean_box(0);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_936_);
v___x_938_ = v___x_915_;
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
v_a_941_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_912_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_912_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* v_e_951_, lean_object* v_checkIfModified_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
uint8_t v_checkIfModified_boxed_958_; lean_object* v_res_959_; 
v_checkIfModified_boxed_958_ = lean_unbox(v_checkIfModified_952_);
v_res_959_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_951_, v_checkIfModified_boxed_958_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_959_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_box(0);
v___x_966_ = l_Lean_Level_succ___override(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_box(0);
v___x_968_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
v___x_971_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
v___x_972_ = l_Lean_mkConst(v___x_971_, v___x_970_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_box(0);
v___x_974_ = l_Lean_mkSort(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_994_ = l_Lean_mkIntLit(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(0);
v___x_1000_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20));
v___x_1001_ = l_Lean_mkConst(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23));
v___x_1008_ = l_Lean_mkConst(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26));
v___x_1015_ = l_Lean_mkConst(v___x_1014_, v___x_1013_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29));
v___x_1022_ = l_Lean_mkConst(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_val_1030_; lean_object* v_h_u2081_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8));
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = l_Lean_Expr_isAppOfArity(v_e_1023_, v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = 1;
v___x_1078_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_1023_, v___x_1077_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_leCarrierIsSort(v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v_leLvl_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v___x_1186_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = l_Lean_Expr_appArg_x21(v_e_1023_);
v___x_1186_ = lean_unbox(v_a_1080_);
lean_dec(v_a_1080_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
v_leLvl_1083_ = v___x_1187_;
v___y_1084_ = v_a_1024_;
v___y_1085_ = v_a_1025_;
v___y_1086_ = v_a_1026_;
v___y_1087_ = v_a_1027_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15);
v_leLvl_1083_ = v___x_1188_;
v___y_1084_ = v_a_1024_;
v___y_1085_ = v_a_1025_;
v___y_1086_ = v_a_1026_;
v___y_1087_ = v_a_1027_;
goto v___jp_1082_;
}
v___jp_1082_:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1081_, v___y_1085_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_Expr_cleanupAnnotations(v_a_1089_);
v___x_1091_ = l_Lean_Expr_isApp(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_dec_ref(v___x_1090_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v_arg_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_arg_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc_ref(v_arg_1092_);
v___x_1093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1090_);
v___x_1094_ = l_Lean_Expr_isApp(v___x_1093_);
if (v___x_1094_ == 0)
{
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v_arg_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_arg_1095_ = lean_ctor_get(v___x_1093_, 1);
lean_inc_ref(v_arg_1095_);
v___x_1096_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1093_);
v___x_1097_ = l_Lean_Expr_isApp(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1096_);
v___x_1099_ = l_Lean_Expr_isApp(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v_arg_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_arg_1100_ = lean_ctor_get(v___x_1098_, 1);
lean_inc_ref(v_arg_1100_);
v___x_1101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1098_);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11));
v___x_1103_ = l_Lean_Expr_isConstOf(v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14));
v___x_1105_ = l_Lean_Expr_isConstOf(v___x_1101_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17));
v___x_1107_ = l_Lean_Expr_isConstOf(v___x_1101_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__18));
v___x_1109_ = l_Lean_Expr_isConstOf(v___x_1101_, v___x_1108_);
lean_dec_ref(v___x_1101_);
if (v___x_1109_ == 0)
{
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1100_, v___y_1085_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = l_Lean_Expr_cleanupAnnotations(v_a_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1114_ = l_Lean_Expr_isConstOf(v___x_1112_, v___x_1113_);
lean_dec_ref(v___x_1112_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1115_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1092_);
v___x_1116_ = l_Lean_mkIntAdd(v_arg_1092_, v___x_1115_);
lean_inc_ref(v_arg_1095_);
lean_inc(v_leLvl_1083_);
v___x_1117_ = l_Lean_mkIntLE(v_leLvl_1083_, v___x_1116_, v_arg_1095_);
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
v___x_1119_ = l_Lean_mkAppB(v___x_1118_, v_arg_1095_, v_arg_1092_);
v_val_1030_ = v___x_1117_;
v_h_u2081_1031_ = v___x_1119_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
goto v___jp_1029_;
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
v_a_1120_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1110_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1110_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
else
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1101_);
v___x_1128_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1100_, v___y_1085_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_Expr_cleanupAnnotations(v_a_1129_);
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1132_ = l_Lean_Expr_isConstOf(v___x_1130_, v___x_1131_);
lean_dec_ref(v___x_1130_);
if (v___x_1132_ == 0)
{
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1133_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1095_);
v___x_1134_ = l_Lean_mkIntAdd(v_arg_1095_, v___x_1133_);
lean_inc_ref(v_arg_1092_);
lean_inc(v_leLvl_1083_);
v___x_1135_ = l_Lean_mkIntLE(v_leLvl_1083_, v___x_1134_, v_arg_1092_);
v___x_1136_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
v___x_1137_ = l_Lean_mkAppB(v___x_1136_, v_arg_1095_, v_arg_1092_);
v_val_1030_ = v___x_1135_;
v_h_u2081_1031_ = v___x_1137_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
goto v___jp_1029_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
v_a_1138_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1128_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1128_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
else
{
lean_object* v___x_1146_; 
lean_dec_ref(v___x_1101_);
v___x_1146_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1100_, v___y_1085_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = l_Lean_Expr_cleanupAnnotations(v_a_1147_);
v___x_1149_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1150_ = l_Lean_Expr_isConstOf(v___x_1148_, v___x_1149_);
lean_dec_ref(v___x_1148_);
if (v___x_1150_ == 0)
{
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_inc_ref(v_arg_1095_);
lean_inc_ref(v_arg_1092_);
lean_inc(v_leLvl_1083_);
v___x_1151_ = l_Lean_mkIntLE(v_leLvl_1083_, v_arg_1092_, v_arg_1095_);
v___x_1152_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
v___x_1153_ = l_Lean_mkAppB(v___x_1152_, v_arg_1095_, v_arg_1092_);
v_val_1030_ = v___x_1151_;
v_h_u2081_1031_ = v___x_1153_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
goto v___jp_1029_;
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
v_a_1154_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1146_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1146_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
else
{
lean_object* v___x_1162_; 
lean_dec_ref(v___x_1101_);
v___x_1162_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1100_, v___y_1085_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_Expr_cleanupAnnotations(v_a_1163_);
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1166_ = l_Lean_Expr_isConstOf(v___x_1164_, v___x_1165_);
lean_dec_ref(v___x_1164_);
if (v___x_1166_ == 0)
{
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc_ref(v_arg_1092_);
lean_inc_ref(v_arg_1095_);
lean_inc(v_leLvl_1083_);
v___x_1167_ = l_Lean_mkIntLE(v_leLvl_1083_, v_arg_1095_, v_arg_1092_);
v___x_1168_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
v___x_1169_ = l_Lean_mkAppB(v___x_1168_, v_arg_1095_, v_arg_1092_);
v_val_1030_ = v___x_1167_;
v_h_u2081_1031_ = v___x_1169_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
goto v___jp_1029_;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_arg_1095_);
lean_dec_ref(v_arg_1092_);
lean_dec_ref(v_e_1023_);
v_a_1170_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1162_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1162_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
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
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_e_1023_);
v_a_1178_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1088_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1088_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_e_1023_);
v_a_1189_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1079_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1079_);
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
v___jp_1029_:
{
uint8_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = 0;
lean_inc_ref(v_val_1030_);
v___x_1037_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_val_1030_, v___x_1036_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1070_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1070_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1070_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
if (lean_obj_tag(v_a_1038_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1064_; 
v_val_1042_ = lean_ctor_get(v_a_1038_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_1038_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1044_ = v_a_1038_;
v_isShared_1045_ = v_isSharedCheck_1064_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_val_1042_);
lean_dec(v_a_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1064_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_fst_1046_; lean_object* v_snd_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1063_; 
v_fst_1046_ = lean_ctor_get(v_val_1042_, 0);
v_snd_1047_ = lean_ctor_get(v_val_1042_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_val_1042_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1049_ = v_val_1042_;
v_isShared_1050_ = v_isSharedCheck_1063_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_snd_1047_);
lean_inc(v_fst_1046_);
lean_dec(v_val_1042_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1063_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1051_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
v___x_1052_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
lean_inc(v_fst_1046_);
v___x_1053_ = l_Lean_mkApp6(v___x_1051_, v___x_1052_, v_e_1023_, v_val_1030_, v_fst_1046_, v_h_u2081_1031_, v_snd_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1053_);
v___x_1055_ = v___x_1049_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_fst_1046_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1055_);
v___x_1057_ = v___x_1044_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1057_);
v___x_1059_ = v___x_1040_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_dec(v_a_1038_);
lean_dec_ref(v_e_1023_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_val_1030_);
lean_ctor_set(v___x_1065_, 1, v_h_u2081_1031_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1066_);
v___x_1068_ = v___x_1040_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_1031_);
lean_dec_ref(v_val_1030_);
lean_dec_ref(v_e_1023_);
return v___x_1037_;
}
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* v_e_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(v_e_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(lean_object* v_snd_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = l_Lean_instInhabitedExpr;
v___x_1207_ = lean_array_get_borrowed(v___x_1206_, v_snd_1204_, v_x_1205_);
lean_inc(v___x_1207_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(lean_object* v_snd_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(v_snd_1208_, v_x_1209_);
lean_dec(v_x_1209_);
lean_dec_ref(v_snd_1208_);
return v_res_1210_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
v___x_1219_ = l_Lean_mkConst(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
v___x_1228_ = l_Lean_mkConst(v___x_1227_, v___x_1226_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
v___x_1237_ = l_Lean_mkConst(v___x_1236_, v___x_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v_h_1247_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1432_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1432_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1432_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 1)
{
lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1427_; 
v_val_1270_ = lean_ctor_get(v_a_1266_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_a_1266_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1272_ = v_a_1266_;
v_isShared_1273_ = v_isSharedCheck_1427_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_dec(v_a_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1427_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_snd_1274_; lean_object* v_fst_1275_; lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1426_; 
v_snd_1274_ = lean_ctor_get(v_val_1270_, 1);
lean_inc(v_snd_1274_);
v_fst_1275_ = lean_ctor_get(v_val_1270_, 0);
lean_inc(v_fst_1275_);
lean_dec(v_val_1270_);
v_fst_1276_ = lean_ctor_get(v_snd_1274_, 0);
v_snd_1277_ = lean_ctor_get(v_snd_1274_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_snd_1274_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1279_ = v_snd_1274_;
v_isShared_1280_ = v_isSharedCheck_1426_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_snd_1277_);
lean_inc(v_fst_1276_);
lean_dec(v_snd_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1426_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___x_1330_; 
v___x_1281_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_1330_ = lean_int_dec_eq(v_fst_1275_, v___x_1281_);
if (v___x_1330_ == 0)
{
lean_object* v___f_1331_; lean_object* v___x_1332_; 
lean_del_object(v___x_1268_);
lean_inc(v_snd_1277_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1331_, 0, v_snd_1277_);
lean_inc(v_fst_1276_);
lean_inc_ref(v___f_1331_);
v___x_1332_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1331_, v_fst_1276_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1413_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1413_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1413_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___y_1338_; uint8_t v___x_1403_; 
v___x_1403_ = lean_int_dec_le(v___x_1281_, v_fst_1275_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1404_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1405_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1406_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1407_ = lean_int_neg(v_fst_1275_);
v___x_1408_ = l_Int_toNat(v___x_1407_);
lean_dec(v___x_1407_);
v___x_1409_ = l_Lean_instToExprInt_mkNat(v___x_1408_);
v___x_1410_ = l_Lean_mkApp3(v___x_1404_, v___x_1405_, v___x_1406_, v___x_1409_);
v___y_1338_ = v___x_1410_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = l_Int_toNat(v_fst_1275_);
v___x_1412_ = l_Lean_instToExprInt_mkNat(v___x_1411_);
v___y_1338_ = v___x_1412_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
lean_inc_ref(v___y_1338_);
v___x_1339_ = l_Lean_mkIntDvd(v___y_1338_, v_a_1333_);
v___x_1340_ = l_Int_Internal_Linear_Expr_norm(v_fst_1276_);
lean_inc(v_fst_1275_);
v___x_1341_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v___x_1340_, v_fst_1275_);
v___x_1342_ = l_Int_Internal_Linear_Poly_getConst(v___x_1340_);
v___x_1343_ = lean_int_emod(v___x_1342_, v___x_1341_);
lean_dec(v___x_1342_);
v___x_1344_ = lean_int_dec_eq(v___x_1343_, v___x_1281_);
lean_dec(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec(v___x_1341_);
lean_dec_ref(v___x_1340_);
lean_del_object(v___x_1335_);
lean_dec_ref(v___f_1331_);
lean_dec(v_fst_1275_);
v___x_1345_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1277_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1366_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1366_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1366_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_1351_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
v___x_1352_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1276_);
v___x_1353_ = l_Lean_eagerReflBoolTrue;
v___x_1354_ = l_Lean_mkApp4(v___x_1351_, v_a_1346_, v___y_1338_, v___x_1352_, v___x_1353_);
v___x_1355_ = l_Lean_mkPropEq(v___x_1339_, v___x_1350_);
v___x_1356_ = l_Lean_Meta_mkExpectedPropHint(v___x_1354_, v___x_1355_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1356_);
lean_ctor_set(v___x_1279_, 0, v___x_1350_);
v___x_1358_ = v___x_1279_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1358_);
v___x_1360_ = v___x_1272_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1360_);
v___x_1362_ = v___x_1348_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v___x_1339_);
lean_dec_ref(v___y_1338_);
lean_del_object(v___x_1279_);
lean_dec(v_fst_1276_);
lean_del_object(v___x_1272_);
v_a_1367_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1345_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1345_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
lean_del_object(v___x_1279_);
lean_del_object(v___x_1272_);
v___x_1375_ = l_Int_Internal_Linear_Poly_div(v___x_1341_, v___x_1340_);
lean_inc_ref(v___x_1375_);
v___x_1376_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1375_);
v___x_1377_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1276_, v___x_1376_);
lean_dec_ref(v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1335_);
lean_inc_ref(v___x_1375_);
v___x_1378_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1331_, v___x_1375_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = lean_int_ediv(v_fst_1275_, v___x_1341_);
lean_dec(v_fst_1275_);
v___x_1381_ = lean_int_dec_le(v___x_1281_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1382_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1383_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1384_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1385_ = lean_int_neg(v___x_1380_);
lean_dec(v___x_1380_);
v___x_1386_ = l_Int_toNat(v___x_1385_);
lean_dec(v___x_1385_);
v___x_1387_ = l_Lean_instToExprInt_mkNat(v___x_1386_);
v___x_1388_ = l_Lean_mkApp3(v___x_1382_, v___x_1383_, v___x_1384_, v___x_1387_);
v___y_1283_ = v___x_1341_;
v___y_1284_ = v_a_1379_;
v___y_1285_ = v___x_1339_;
v___y_1286_ = v___x_1375_;
v___y_1287_ = v___y_1338_;
v___y_1288_ = v___x_1388_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = l_Int_toNat(v___x_1380_);
lean_dec(v___x_1380_);
v___x_1390_ = l_Lean_instToExprInt_mkNat(v___x_1389_);
v___y_1283_ = v___x_1341_;
v___y_1284_ = v_a_1379_;
v___y_1285_ = v___x_1339_;
v___y_1286_ = v___x_1375_;
v___y_1287_ = v___y_1338_;
v___y_1288_ = v___x_1390_;
goto v___jp_1282_;
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v___x_1375_);
lean_dec(v___x_1341_);
lean_dec_ref(v___x_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v_snd_1277_);
lean_dec(v_fst_1276_);
lean_dec(v_fst_1275_);
v_a_1391_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1378_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1378_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec_ref(v___x_1375_);
lean_dec(v___x_1341_);
lean_dec_ref(v___x_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___f_1331_);
lean_dec(v_snd_1277_);
lean_dec(v_fst_1276_);
lean_dec(v_fst_1275_);
v___x_1399_ = lean_box(0);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1399_);
v___x_1401_ = v___x_1335_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v___f_1331_);
lean_del_object(v___x_1279_);
lean_dec(v_snd_1277_);
lean_dec(v_fst_1276_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1272_);
v_a_1414_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1332_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1332_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_del_object(v___x_1279_);
lean_dec(v_snd_1277_);
lean_dec(v_fst_1276_);
lean_dec(v_fst_1275_);
lean_del_object(v___x_1272_);
v___x_1422_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1422_);
v___x_1424_ = v___x_1268_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
v___jp_1282_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
lean_inc_ref(v___y_1288_);
v___x_1289_ = l_Lean_mkIntDvd(v___y_1288_, v___y_1284_);
v___x_1290_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_1291_ = lean_int_dec_eq(v___y_1283_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1277_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
v___x_1295_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1276_);
v___x_1296_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1286_);
v___x_1297_ = lean_int_dec_le(v___x_1281_, v___y_1283_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1298_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1299_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1300_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1301_ = lean_int_neg(v___y_1283_);
lean_dec(v___y_1283_);
v___x_1302_ = l_Int_toNat(v___x_1301_);
lean_dec(v___x_1301_);
v___x_1303_ = l_Lean_instToExprInt_mkNat(v___x_1302_);
v___x_1304_ = l_Lean_mkApp3(v___x_1298_, v___x_1299_, v___x_1300_, v___x_1303_);
v___y_1254_ = v___x_1296_;
v___y_1255_ = v___y_1285_;
v___y_1256_ = v_a_1293_;
v___y_1257_ = v___x_1289_;
v___y_1258_ = v___y_1288_;
v___y_1259_ = v___x_1294_;
v___y_1260_ = v___x_1295_;
v___y_1261_ = v___y_1287_;
v___y_1262_ = v___x_1304_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = l_Int_toNat(v___y_1283_);
lean_dec(v___y_1283_);
v___x_1306_ = l_Lean_instToExprInt_mkNat(v___x_1305_);
v___y_1254_ = v___x_1296_;
v___y_1255_ = v___y_1285_;
v___y_1256_ = v_a_1293_;
v___y_1257_ = v___x_1289_;
v___y_1258_ = v___y_1288_;
v___y_1259_ = v___x_1294_;
v___y_1260_ = v___x_1295_;
v___y_1261_ = v___y_1287_;
v___y_1262_ = v___x_1306_;
goto v___jp_1253_;
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1283_);
lean_dec(v_fst_1276_);
v_a_1307_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1292_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1292_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v___x_1315_; 
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1283_);
v___x_1315_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1277_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
v___x_1318_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1276_);
v___x_1319_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1286_);
v___x_1320_ = l_Lean_eagerReflBoolTrue;
v___x_1321_ = l_Lean_mkApp5(v___x_1317_, v_a_1316_, v___y_1287_, v___x_1318_, v___x_1319_, v___x_1320_);
v___y_1245_ = v___y_1285_;
v___y_1246_ = v___x_1289_;
v_h_1247_ = v___x_1321_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_fst_1276_);
v_a_1322_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1315_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1315_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
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
lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec(v_a_1266_);
v___x_1428_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1428_);
v___x_1430_ = v___x_1268_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1265_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1265_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
v___jp_1244_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_inc_ref(v___y_1246_);
v___x_1248_ = l_Lean_mkPropEq(v___y_1245_, v___y_1246_);
v___x_1249_ = l_Lean_Meta_mkExpectedPropHint(v_h_1247_, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___y_1246_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
v___jp_1253_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_1259_);
v___x_1264_ = l_Lean_mkApp7(v___y_1259_, v___y_1256_, v___y_1261_, v___y_1260_, v___y_1258_, v___y_1254_, v___y_1262_, v___x_1263_);
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___y_1257_;
v_h_1247_ = v___x_1264_;
goto v___jp_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* v_e_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(v_e_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1447_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
v___x_1458_ = l_Lean_mkConst(v___x_1457_, v___x_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* v_lhs_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_lhs_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1532_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1532_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1532_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_fst_1470_; lean_object* v_snd_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1531_; 
v_fst_1470_ = lean_ctor_get(v_a_1466_, 0);
v_snd_1471_ = lean_ctor_get(v_a_1466_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_a_1466_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1473_ = v_a_1466_;
v_isShared_1474_ = v_isSharedCheck_1531_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snd_1471_);
lean_inc(v_fst_1470_);
lean_dec(v_a_1466_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1531_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = l_Int_Internal_Linear_Expr_norm(v_fst_1470_);
lean_inc_ref(v___x_1475_);
v___x_1476_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1475_);
v___x_1477_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1470_, v___x_1476_);
lean_dec_ref(v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_del_object(v___x_1468_);
lean_inc(v_snd_1471_);
v___x_1478_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1471_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1480_, 0, v_snd_1471_);
lean_inc(v_fst_1470_);
v___x_1481_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1470_);
lean_inc_ref(v___f_1480_);
v___x_1482_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1480_, v_fst_1470_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
lean_inc_ref(v___x_1475_);
v___x_1484_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1475_);
v___x_1485_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1480_, v___x_1475_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1502_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1502_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1502_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1490_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
v___x_1491_ = l_Lean_eagerReflBoolTrue;
v___x_1492_ = l_Lean_mkApp4(v___x_1490_, v_a_1479_, v___x_1481_, v___x_1484_, v___x_1491_);
lean_inc(v_a_1486_);
v___x_1493_ = l_Lean_mkIntEq(v_a_1483_, v_a_1486_);
v___x_1494_ = l_Lean_Meta_mkExpectedPropHint(v___x_1492_, v___x_1493_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1494_);
lean_ctor_set(v___x_1473_, 0, v_a_1486_);
v___x_1496_ = v___x_1473_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1497_);
v___x_1499_ = v___x_1488_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v___x_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v___x_1481_);
lean_dec(v_a_1479_);
lean_del_object(v___x_1473_);
v_a_1503_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1485_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1485_);
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
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v___x_1481_);
lean_dec_ref(v___f_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v___x_1475_);
lean_del_object(v___x_1473_);
v_a_1511_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1482_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1482_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1475_);
lean_del_object(v___x_1473_);
lean_dec(v_snd_1471_);
lean_dec(v_fst_1470_);
v_a_1519_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1478_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1478_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
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
lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_dec_ref(v___x_1475_);
lean_del_object(v___x_1473_);
lean_dec(v_snd_1471_);
lean_dec(v_fst_1470_);
v___x_1527_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1527_);
v___x_1529_ = v___x_1468_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
v_a_1533_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1465_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1465_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* v_lhs_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(v_lhs_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
return v_res_1547_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
}
#ifdef __cplusplus
}
#endif
