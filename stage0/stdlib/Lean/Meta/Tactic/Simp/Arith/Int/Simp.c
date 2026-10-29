// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object*);
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
uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "eq_eq_false_of_divCoeff_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(186, 201, 183, 205, 148, 206, 35, 35)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "norm_eq_coeff_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(26, 10, 48, 215, 225, 31, 230, 249)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "norm_eq_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(251, 163, 246, 73, 9, 174, 23, 99)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "norm_eq_var_const_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(236, 215, 111, 153, 219, 202, 88, 30)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_eq_var_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value),LEAN_SCALAR_PTR_LITERAL(186, 129, 136, 100, 163, 147, 30, 176)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "eq_eq_true_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(9, 28, 141, 228, 181, 95, 165, 158)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_eq_false_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(40, 101, 72, 170, 22, 188, 204, 54)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "norm_le_coeff_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 43, 64, 104, 55, 2, 154, 187)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "norm_le_coeff_tight_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 18, 27, 86, 242, 246, 103, 255)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "norm_le_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 178, 20, 8, 20, 241, 64, 31)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_eq_true_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(164, 96, 66, 240, 24, 135, 42, 34)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "le_eq_false_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(247, 96, 152, 201, 233, 33, 159, 24)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value;
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_ge_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(87, 141, 152, 40, 61, 44, 151, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_lt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(214, 41, 233, 126, 147, 68, 29, 47)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_gt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 48, 12, 204, 229, 102, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "norm_dvd_gcd_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 38, 133, 67, 94, 41, 13)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "norm_dvd_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(5, 165, 25, 74, 41, 128, 38, 221)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dvd_eq_false_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(117, 102, 106, 70, 60, 85, 98, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "eq_of_norm_eq_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(8, 59, 192, 17, 181, 145, 15, 206)}};
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2));
v___x_62_ = l_Lean_mkConst(v___x_61_, v___x_60_);
return v___x_62_;
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Level_ofNat(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14);
v___x_86_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12));
v___x_87_ = l_Lean_Expr_const___override(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_box(0);
v___x_91_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16));
v___x_92_ = l_Lean_Expr_const___override(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_box(0);
v___x_98_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_99_ = l_Lean_Expr_const___override(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_101_ = l_Lean_mkIntLit(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23));
v___x_110_ = l_Lean_mkConst(v___x_109_, v___x_108_);
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_to_int(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
v___x_131_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31));
v___x_132_ = l_Lean_mkConst(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
v___x_134_ = lean_int_neg(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
v___x_142_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35));
v___x_143_ = l_Lean_mkConst(v___x_142_, v___x_141_);
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
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Lean_instInhabitedExpr;
v___x_175_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_564_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_564_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_564_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_564_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
if (lean_obj_tag(v_a_176_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_559_; 
v_val_180_ = lean_ctor_get(v_a_176_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_559_ == 0)
{
v___x_182_ = v_a_176_;
v_isShared_183_ = v_isSharedCheck_559_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v_a_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_559_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_snd_184_; lean_object* v_fst_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_558_; 
v_snd_184_ = lean_ctor_get(v_val_180_, 1);
v_fst_185_ = lean_ctor_get(v_val_180_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_val_180_);
if (v_isSharedCheck_558_ == 0)
{
v___x_187_ = v_val_180_;
v_isShared_188_ = v_isSharedCheck_558_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_snd_184_);
lean_inc(v_fst_185_);
lean_dec(v_val_180_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_558_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_557_; 
v_fst_189_ = lean_ctor_get(v_snd_184_, 0);
v_snd_190_ = lean_ctor_get(v_snd_184_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_snd_184_);
if (v_isSharedCheck_557_ == 0)
{
v___x_192_ = v_snd_184_;
v_isShared_193_ = v_isSharedCheck_557_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snd_190_);
lean_inc(v_fst_189_);
lean_dec(v_snd_184_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_557_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___f_194_; lean_object* v___x_195_; 
lean_inc(v_snd_190_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_194_, 0, v___x_174_);
lean_closure_set(v___f_194_, 1, v_snd_190_);
lean_inc(v_fst_185_);
lean_inc_ref(v___f_194_);
v___x_195_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_185_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_548_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_548_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_548_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_548_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; 
lean_inc(v_fst_189_);
lean_inc_ref(v___f_194_);
v___x_200_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_189_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_539_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_539_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_539_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_539_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___x_373_; 
v___x_205_ = l_Lean_mkIntEq(v_a_196_, v_a_201_);
lean_inc(v_fst_189_);
lean_inc(v_fst_185_);
v___x_245_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_245_, 0, v_fst_185_);
lean_ctor_set(v___x_245_, 1, v_fst_189_);
v___x_246_ = l_Int_Internal_Linear_Expr_norm(v___x_245_);
lean_dec_ref_known(v___x_245_, 2);
v___x_373_ = l_Int_Internal_Linear_Poly_isUnsatEq(v___x_246_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; 
v___x_374_ = l_Int_Internal_Linear_Poly_isValidEq(v___x_246_);
if (v___x_374_ == 0)
{
if (lean_obj_tag(v___x_246_) == 1)
{
lean_object* v_k_375_; lean_object* v_v_376_; lean_object* v_p_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_k_375_ = lean_ctor_get(v___x_246_, 0);
v_v_376_ = lean_ctor_get(v___x_246_, 1);
v_p_377_ = lean_ctor_get(v___x_246_, 2);
lean_inc_ref(v_p_377_);
v___x_378_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
v___x_379_ = lean_int_dec_eq(v_k_375_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec_ref(v_p_377_);
v___y_361_ = v_a_169_;
v___y_362_ = v_a_170_;
v___y_363_ = v_a_171_;
v___y_364_ = v_a_172_;
goto v___jp_360_;
}
else
{
if (lean_obj_tag(v_p_377_) == 0)
{
lean_object* v_k_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_434_; 
lean_inc(v_v_376_);
lean_dec_ref_known(v___x_246_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v_k_380_ = lean_ctor_get(v_p_377_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_p_377_);
if (v_isSharedCheck_434_ == 0)
{
v___x_382_ = v_p_377_;
v_isShared_383_ = v_isSharedCheck_434_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_k_380_);
lean_dec(v_p_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_434_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___y_386_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_384_ = lean_array_get_borrowed(v___x_174_, v_snd_190_, v_v_376_);
v___x_422_ = lean_int_neg(v_k_380_);
lean_dec(v_k_380_);
v___x_423_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_424_ = lean_int_dec_le(v___x_423_, v___x_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_426_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_427_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_428_ = lean_int_neg(v___x_422_);
lean_dec(v___x_422_);
v___x_429_ = l_Int_toNat(v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = l_Lean_instToExprInt_mkNat(v___x_429_);
v___x_431_ = l_Lean_mkApp3(v___x_425_, v___x_426_, v___x_427_, v___x_430_);
v___y_386_ = v___x_431_;
goto v___jp_385_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = l_Int_toNat(v___x_422_);
lean_dec(v___x_422_);
v___x_433_ = l_Lean_instToExprInt_mkNat(v___x_432_);
v___y_386_ = v___x_433_;
goto v___jp_385_;
}
v___jp_385_:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
lean_inc_ref(v___y_386_);
lean_inc(v___x_384_);
v___x_387_ = l_Lean_mkIntEq(v___x_384_, v___y_386_);
v___x_388_ = lean_expr_eqv(v___x_387_, v___x_205_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_409_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_409_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_409_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_394_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32);
v___x_395_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_396_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_397_ = l_Lean_mkNatLit(v_v_376_);
v___x_398_ = l_Lean_eagerReflBoolTrue;
v___x_399_ = l_Lean_mkApp6(v___x_394_, v_a_390_, v___x_395_, v___x_396_, v___x_397_, v___y_386_, v___x_398_);
lean_inc_ref(v___x_387_);
v___x_400_ = l_Lean_mkPropEq(v___x_205_, v___x_387_);
v___x_401_ = l_Lean_Meta_mkExpectedPropHint(v___x_399_, v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_387_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 1);
lean_ctor_set(v___x_382_, 0, v___x_402_);
v___x_404_ = v___x_382_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_404_);
v___x_406_ = v___x_392_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v___y_386_);
lean_del_object(v___x_382_);
lean_dec(v_v_376_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_410_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_389_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v___y_386_);
lean_dec(v_v_376_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v___x_418_ = lean_box(0);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_418_);
v___x_420_ = v___x_382_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
else
{
lean_object* v_k_435_; lean_object* v_v_436_; lean_object* v_p_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_k_435_ = lean_ctor_get(v_p_377_, 0);
lean_inc(v_k_435_);
v_v_436_ = lean_ctor_get(v_p_377_, 1);
lean_inc(v_v_436_);
v_p_437_ = lean_ctor_get(v_p_377_, 2);
lean_inc_ref(v_p_437_);
lean_dec_ref_known(v_p_377_, 3);
v___x_438_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33);
v___x_439_ = lean_int_dec_eq(v_k_435_, v___x_438_);
lean_dec(v_k_435_);
if (v___x_439_ == 0)
{
lean_dec_ref(v_p_437_);
lean_dec(v_v_436_);
v___y_361_ = v_a_169_;
v___y_362_ = v_a_170_;
v___y_363_ = v_a_171_;
v___y_364_ = v_a_172_;
goto v___jp_360_;
}
else
{
if (lean_obj_tag(v_p_437_) == 0)
{
lean_object* v_k_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_484_; 
v_k_440_ = lean_ctor_get(v_p_437_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_p_437_);
if (v_isSharedCheck_484_ == 0)
{
v___x_442_ = v_p_437_;
v_isShared_443_ = v_isSharedCheck_484_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_k_440_);
lean_dec(v_p_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_484_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_445_ = lean_int_dec_eq(v_k_440_, v___x_444_);
lean_dec(v_k_440_);
if (v___x_445_ == 0)
{
lean_del_object(v___x_442_);
lean_dec(v_v_436_);
v___y_361_ = v_a_169_;
v___y_362_ = v_a_170_;
v___y_363_ = v_a_171_;
v___y_364_ = v_a_172_;
goto v___jp_360_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
lean_inc(v_v_376_);
lean_dec_ref_known(v___x_246_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v___x_446_ = lean_array_get_borrowed(v___x_174_, v_snd_190_, v_v_376_);
v___x_447_ = lean_array_get_borrowed(v___x_174_, v_snd_190_, v_v_436_);
lean_inc(v___x_447_);
lean_inc(v___x_446_);
v___x_448_ = l_Lean_mkIntEq(v___x_446_, v___x_447_);
v___x_449_ = lean_expr_eqv(v___x_448_, v___x_205_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_471_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_471_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_471_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_471_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_455_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_456_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_457_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_458_ = l_Lean_mkNatLit(v_v_376_);
v___x_459_ = l_Lean_mkNatLit(v_v_436_);
v___x_460_ = l_Lean_eagerReflBoolTrue;
v___x_461_ = l_Lean_mkApp6(v___x_455_, v_a_451_, v___x_456_, v___x_457_, v___x_458_, v___x_459_, v___x_460_);
lean_inc_ref(v___x_448_);
v___x_462_ = l_Lean_mkPropEq(v___x_205_, v___x_448_);
v___x_463_ = l_Lean_Meta_mkExpectedPropHint(v___x_461_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_448_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 1);
lean_ctor_set(v___x_442_, 0, v___x_464_);
v___x_466_ = v___x_442_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_466_);
v___x_468_ = v___x_453_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v___x_448_);
lean_del_object(v___x_442_);
lean_dec(v_v_436_);
lean_dec(v_v_376_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_472_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_450_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_450_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v___x_448_);
lean_dec(v_v_436_);
lean_dec(v_v_376_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v___x_480_ = lean_box(0);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_480_);
v___x_482_ = v___x_442_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_437_);
lean_dec(v_v_436_);
v___y_361_ = v_a_169_;
v___y_362_ = v_a_170_;
v___y_363_ = v_a_171_;
v___y_364_ = v_a_172_;
goto v___jp_360_;
}
}
}
}
}
else
{
v___y_361_ = v_a_169_;
v___y_362_ = v_a_170_;
v___y_363_ = v_a_171_;
v___y_364_ = v_a_172_;
goto v___jp_360_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec_ref(v___x_246_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v___x_485_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_486_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_503_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_503_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_491_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42);
v___x_492_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_493_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_494_ = l_Lean_eagerReflBoolTrue;
v___x_495_ = l_Lean_mkApp4(v___x_491_, v_a_487_, v___x_492_, v___x_493_, v___x_494_);
v___x_496_ = l_Lean_mkPropEq(v___x_205_, v___x_485_);
v___x_497_ = l_Lean_Meta_mkExpectedPropHint(v___x_495_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_485_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_499_);
v___x_501_ = v___x_489_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_504_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_486_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_486_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v___x_246_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v___x_512_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3);
v___x_513_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_530_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_530_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_518_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45);
v___x_519_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_520_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_521_ = l_Lean_eagerReflBoolTrue;
v___x_522_ = l_Lean_mkApp4(v___x_518_, v_a_514_, v___x_519_, v___x_520_, v___x_521_);
v___x_523_ = l_Lean_mkPropEq(v___x_205_, v___x_512_);
v___x_524_ = l_Lean_Meta_mkExpectedPropHint(v___x_522_, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_512_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_531_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_513_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_513_);
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
v___jp_206_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_213_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_209_);
v___x_214_ = l_Lean_mkApp5(v___y_209_, v___y_207_, v___y_210_, v___y_208_, v___y_212_, v___x_213_);
lean_inc_ref_n(v___y_211_, 2);
v___x_215_ = l_Lean_mkPropEq(v___x_205_, v___y_211_);
v___x_216_ = l_Lean_Meta_mkExpectedPropHint(v___x_214_, v___x_215_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_216_);
lean_ctor_set(v___x_192_, 0, v___y_211_);
v___x_218_ = v___x_192_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___y_211_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_218_);
v___x_220_ = v___x_182_;
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
lean_inc_ref(v___y_232_);
v___x_235_ = l_Lean_mkApp6(v___y_232_, v___y_229_, v___y_230_, v___y_227_, v___y_231_, v___y_233_, v___x_234_);
lean_inc_ref(v___y_228_);
v___x_236_ = l_Lean_mkPropEq(v___x_205_, v___y_228_);
v___x_237_ = l_Lean_Meta_mkExpectedPropHint(v___x_235_, v___x_236_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___x_237_);
lean_ctor_set(v___x_187_, 0, v___y_228_);
v___x_239_ = v___x_187_;
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
v___jp_247_:
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___x_246_);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_dec_eq(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_255_ = l_Int_Internal_Linear_Poly_getConst(v___x_246_);
v___x_256_ = lean_nat_to_int(v___x_252_);
v___x_257_ = lean_int_emod(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_259_ = lean_int_dec_eq(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref(v___x_246_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_187_);
v___x_260_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3);
v___x_261_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v___y_249_, v___y_248_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_264_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_265_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_266_ = lean_int_dec_le(v___x_258_, v___x_256_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_268_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_269_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_270_ = lean_int_neg(v___x_256_);
lean_dec(v___x_256_);
v___x_271_ = l_Int_toNat(v___x_270_);
lean_dec(v___x_270_);
v___x_272_ = l_Lean_instToExprInt_mkNat(v___x_271_);
v___x_273_ = l_Lean_mkApp3(v___x_267_, v___x_268_, v___x_269_, v___x_272_);
v___y_207_ = v_a_262_;
v___y_208_ = v___x_265_;
v___y_209_ = v___x_263_;
v___y_210_ = v___x_264_;
v___y_211_ = v___x_260_;
v___y_212_ = v___x_273_;
goto v___jp_206_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_Int_toNat(v___x_256_);
lean_dec(v___x_256_);
v___x_275_ = l_Lean_instToExprInt_mkNat(v___x_274_);
v___y_207_ = v_a_262_;
v___y_208_ = v___x_265_;
v___y_209_ = v___x_263_;
v___y_210_ = v___x_264_;
v___y_211_ = v___x_260_;
v___y_212_ = v___x_275_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v___x_256_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_203_);
lean_del_object(v___x_192_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
v_a_276_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_261_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_261_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_203_);
lean_del_object(v___x_192_);
lean_del_object(v___x_182_);
v___x_284_ = l_Int_Internal_Linear_Poly_div(v___x_256_, v___x_246_);
lean_inc_ref(v___x_284_);
v___x_285_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21);
v___x_288_ = l_Lean_mkIntEq(v_a_286_, v___x_287_);
v___x_289_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v___y_249_, v___y_248_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v___x_289_, 1);
v___x_291_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_292_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_293_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_294_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_284_);
v___x_295_ = lean_int_dec_le(v___x_258_, v___x_256_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_297_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_298_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_299_ = lean_int_neg(v___x_256_);
lean_dec(v___x_256_);
v___x_300_ = l_Int_toNat(v___x_299_);
lean_dec(v___x_299_);
v___x_301_ = l_Lean_instToExprInt_mkNat(v___x_300_);
v___x_302_ = l_Lean_mkApp3(v___x_296_, v___x_297_, v___x_298_, v___x_301_);
v___y_227_ = v___x_293_;
v___y_228_ = v___x_288_;
v___y_229_ = v_a_290_;
v___y_230_ = v___x_292_;
v___y_231_ = v___x_294_;
v___y_232_ = v___x_291_;
v___y_233_ = v___x_302_;
goto v___jp_226_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = l_Int_toNat(v___x_256_);
lean_dec(v___x_256_);
v___x_304_ = l_Lean_instToExprInt_mkNat(v___x_303_);
v___y_227_ = v___x_293_;
v___y_228_ = v___x_288_;
v___y_229_ = v_a_290_;
v___y_230_ = v___x_292_;
v___y_231_ = v___x_294_;
v___y_232_ = v___x_291_;
v___y_233_ = v___x_304_;
goto v___jp_226_;
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v___x_288_);
lean_dec_ref(v___x_284_);
lean_dec(v___x_256_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
v_a_305_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_289_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_289_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v___x_284_);
lean_dec(v___x_256_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
v_a_313_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_285_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_285_);
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
}
else
{
lean_object* v___x_321_; 
lean_dec(v___x_252_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_inc_ref(v___x_246_);
v___x_321_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_246_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21);
v___x_324_ = l_Lean_mkIntEq(v_a_322_, v___x_323_);
v___x_325_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v___y_249_, v___y_248_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_343_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_343_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_343_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_343_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_330_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27);
v___x_331_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_332_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_333_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_246_);
v___x_334_ = l_Lean_eagerReflBoolTrue;
v___x_335_ = l_Lean_mkApp5(v___x_330_, v_a_326_, v___x_331_, v___x_332_, v___x_333_, v___x_334_);
lean_inc_ref(v___x_324_);
v___x_336_ = l_Lean_mkPropEq(v___x_205_, v___x_324_);
v___x_337_ = l_Lean_Meta_mkExpectedPropHint(v___x_335_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_324_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_339_);
v___x_341_ = v___x_328_;
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
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v___x_246_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_344_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_325_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_325_);
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
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___x_246_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_352_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_321_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_321_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
v___jp_360_:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
lean_inc_ref(v___x_246_);
v___x_365_ = l_Int_Internal_Linear_Poly_toExpr(v___x_246_);
v___x_366_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_365_, v_fst_185_);
lean_dec_ref(v___x_365_);
if (v___x_366_ == 0)
{
lean_del_object(v___x_178_);
v___y_248_ = v___y_362_;
v___y_249_ = v___y_361_;
v___y_250_ = v___y_363_;
v___y_251_ = v___y_364_;
goto v___jp_247_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28);
v___x_368_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_189_, v___x_367_);
if (v___x_368_ == 0)
{
lean_del_object(v___x_178_);
v___y_248_ = v___y_362_;
v___y_249_ = v___y_361_;
v___y_250_ = v___y_363_;
v___y_251_ = v___y_364_;
goto v___jp_247_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v___x_246_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
v___x_369_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_369_);
v___x_371_ = v___x_178_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_198_);
lean_dec(v_a_196_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v_a_540_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_200_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_200_);
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
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v_a_549_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_195_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_195_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec(v_a_176_);
v___x_560_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_560_);
v___x_562_ = v___x_178_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_175_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_175_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* v_e_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(v_e_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_579_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
v___x_588_ = l_Lean_mkConst(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
v___x_597_ = l_Lean_mkConst(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
v___x_606_ = l_Lean_mkConst(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_box(0);
v___x_614_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
v___x_615_ = l_Lean_mkConst(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_box(0);
v___x_623_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
v___x_624_ = l_Lean_mkConst(v___x_623_, v___x_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* v_e_630_, uint8_t v_checkIfModified_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v_h_640_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; uint8_t v___y_678_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___x_804_; uint8_t v___y_806_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_804_ = l_Lean_instInhabitedExpr;
v___x_944_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_945_ = l_Lean_Expr_isAppOf(v_e_630_, v___x_944_);
if (v___x_945_ == 0)
{
v___y_806_ = v___x_945_;
goto v___jp_805_;
}
else
{
v___y_806_ = v_checkIfModified_631_;
goto v___jp_805_;
}
v___jp_637_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_inc_ref(v___y_638_);
v___x_641_ = l_Lean_mkPropEq(v___y_639_, v___y_638_);
v___x_642_ = l_Lean_Meta_mkExpectedPropHint(v_h_640_, v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___y_638_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
v___jp_646_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_651_);
v___x_656_ = l_Lean_mkApp6(v___y_651_, v___y_647_, v___y_652_, v___y_653_, v___y_649_, v___y_654_, v___x_655_);
v___y_638_ = v___y_648_;
v___y_639_ = v___y_650_;
v_h_640_ = v___x_656_;
goto v___jp_637_;
}
v___jp_657_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_664_);
v___x_667_ = l_Lean_mkApp6(v___y_664_, v___y_658_, v___y_662_, v___y_660_, v___y_663_, v___y_665_, v___x_666_);
v___y_638_ = v___y_659_;
v___y_639_ = v___y_661_;
v_h_640_ = v___x_667_;
goto v___jp_637_;
}
v___jp_668_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = l_Int_Internal_Linear_Poly_div(v___y_676_, v___y_677_);
lean_inc_ref(v___x_679_);
v___x_680_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_670_, v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = l_Lean_mkIntLit(v___y_669_);
v___x_683_ = l_Lean_mkIntLE(v_a_681_, v___x_682_);
if (v___y_678_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_672_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_box(0);
v___x_687_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
v___x_688_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_673_);
v___x_689_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_674_);
v___x_690_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_679_);
v___x_691_ = lean_int_dec_le(v___y_669_, v___y_676_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_692_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12));
v___x_693_ = l_Lean_Level_ofNat(v___y_671_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_686_);
v___x_695_ = l_Lean_Expr_const___override(v___x_692_, v___x_694_);
v___x_696_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_697_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_698_ = lean_int_neg(v___y_676_);
lean_dec(v___y_676_);
v___x_699_ = l_Int_toNat(v___x_698_);
lean_dec(v___x_698_);
v___x_700_ = l_Lean_instToExprInt_mkNat(v___x_699_);
v___x_701_ = l_Lean_mkApp3(v___x_695_, v___x_696_, v___x_697_, v___x_700_);
v___y_658_ = v_a_685_;
v___y_659_ = v___x_683_;
v___y_660_ = v___x_689_;
v___y_661_ = v___y_675_;
v___y_662_ = v___x_688_;
v___y_663_ = v___x_690_;
v___y_664_ = v___x_687_;
v___y_665_ = v___x_701_;
goto v___jp_657_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = l_Int_toNat(v___y_676_);
lean_dec(v___y_676_);
v___x_703_ = l_Lean_instToExprInt_mkNat(v___x_702_);
v___y_658_ = v_a_685_;
v___y_659_ = v___x_683_;
v___y_660_ = v___x_689_;
v___y_661_ = v___y_675_;
v___y_662_ = v___x_688_;
v___y_663_ = v___x_690_;
v___y_664_ = v___x_687_;
v___y_665_ = v___x_703_;
goto v___jp_657_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_679_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___y_673_);
v_a_704_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_684_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_684_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_672_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = lean_box(0);
v___x_715_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
v___x_716_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_673_);
v___x_717_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_674_);
v___x_718_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_679_);
v___x_719_ = lean_int_dec_le(v___y_669_, v___y_676_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_720_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12));
v___x_721_ = l_Lean_Level_ofNat(v___y_671_);
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_714_);
v___x_723_ = l_Lean_Expr_const___override(v___x_720_, v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_725_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_726_ = lean_int_neg(v___y_676_);
lean_dec(v___y_676_);
v___x_727_ = l_Int_toNat(v___x_726_);
lean_dec(v___x_726_);
v___x_728_ = l_Lean_instToExprInt_mkNat(v___x_727_);
v___x_729_ = l_Lean_mkApp3(v___x_723_, v___x_724_, v___x_725_, v___x_728_);
v___y_647_ = v_a_713_;
v___y_648_ = v___x_683_;
v___y_649_ = v___x_718_;
v___y_650_ = v___y_675_;
v___y_651_ = v___x_715_;
v___y_652_ = v___x_716_;
v___y_653_ = v___x_717_;
v___y_654_ = v___x_729_;
goto v___jp_646_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = l_Int_toNat(v___y_676_);
lean_dec(v___y_676_);
v___x_731_ = l_Lean_instToExprInt_mkNat(v___x_730_);
v___y_647_ = v_a_713_;
v___y_648_ = v___x_683_;
v___y_649_ = v___x_718_;
v___y_650_ = v___y_675_;
v___y_651_ = v___x_715_;
v___y_652_ = v___x_716_;
v___y_653_ = v___x_717_;
v___y_654_ = v___x_731_;
goto v___jp_646_;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___x_683_);
lean_dec_ref(v___x_679_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___y_673_);
v_a_732_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_712_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_712_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___x_679_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v___y_672_);
v_a_740_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_680_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_680_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
v___jp_748_:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___y_754_);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_dec_eq(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_758_ = l_Int_Internal_Linear_Poly_getConst(v___y_754_);
v___x_759_ = lean_nat_to_int(v___x_755_);
v___x_760_ = lean_int_emod(v___x_758_, v___x_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_763_ = lean_int_dec_eq(v___x_760_, v___x_762_);
lean_dec(v___x_760_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; 
v___x_764_ = 1;
v___y_669_ = v___x_762_;
v___y_670_ = v___y_749_;
v___y_671_ = v___x_761_;
v___y_672_ = v___y_750_;
v___y_673_ = v___y_751_;
v___y_674_ = v___y_753_;
v___y_675_ = v___y_752_;
v___y_676_ = v___x_759_;
v___y_677_ = v___y_754_;
v___y_678_ = v___x_764_;
goto v___jp_668_;
}
else
{
v___y_669_ = v___x_762_;
v___y_670_ = v___y_749_;
v___y_671_ = v___x_761_;
v___y_672_ = v___y_750_;
v___y_673_ = v___y_751_;
v___y_674_ = v___y_753_;
v___y_675_ = v___y_752_;
v___y_676_ = v___x_759_;
v___y_677_ = v___y_754_;
v___y_678_ = v___x_757_;
goto v___jp_668_;
}
}
else
{
lean_object* v___x_765_; 
lean_dec(v___x_755_);
lean_inc_ref(v___y_754_);
v___x_765_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_749_, v___y_754_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21);
v___x_768_ = l_Lean_mkIntLE(v_a_766_, v___x_767_);
v___x_769_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_750_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_787_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_774_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
v___x_775_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_751_);
v___x_776_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_753_);
v___x_777_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_754_);
v___x_778_ = l_Lean_eagerReflBoolTrue;
v___x_779_ = l_Lean_mkApp5(v___x_774_, v_a_770_, v___x_775_, v___x_776_, v___x_777_, v___x_778_);
lean_inc_ref(v___x_768_);
v___x_780_ = l_Lean_mkPropEq(v___y_752_, v___x_768_);
v___x_781_ = l_Lean_Meta_mkExpectedPropHint(v___x_779_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_768_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_783_);
v___x_785_ = v___x_772_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v___x_768_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v___y_751_);
v_a_788_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_769_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_769_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v___y_750_);
v_a_796_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_765_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_765_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
v___jp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_935_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_935_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_935_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_935_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (lean_obj_tag(v_a_808_) == 1)
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_810_);
v_val_812_ = lean_ctor_get(v_a_808_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_930_ == 0)
{
v___x_814_ = v_a_808_;
v_isShared_815_ = v_isSharedCheck_930_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v_a_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_930_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_snd_816_; lean_object* v_fst_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_929_; 
v_snd_816_ = lean_ctor_get(v_val_812_, 1);
v_fst_817_ = lean_ctor_get(v_val_812_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_val_812_);
if (v_isSharedCheck_929_ == 0)
{
v___x_819_ = v_val_812_;
v_isShared_820_ = v_isSharedCheck_929_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snd_816_);
lean_inc(v_fst_817_);
lean_dec(v_val_812_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_929_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_fst_821_; lean_object* v_snd_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_928_; 
v_fst_821_ = lean_ctor_get(v_snd_816_, 0);
v_snd_822_ = lean_ctor_get(v_snd_816_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_snd_816_);
if (v_isSharedCheck_928_ == 0)
{
v___x_824_ = v_snd_816_;
v_isShared_825_ = v_isSharedCheck_928_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_snd_822_);
lean_inc(v_fst_821_);
lean_dec(v_snd_816_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_928_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___f_826_; lean_object* v___x_827_; 
lean_inc(v_snd_822_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_826_, 0, v___x_804_);
lean_closure_set(v___f_826_, 1, v_snd_822_);
lean_inc(v_fst_817_);
lean_inc_ref(v___f_826_);
v___x_827_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_826_, v_fst_817_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
lean_inc(v_fst_821_);
lean_inc_ref(v___f_826_);
v___x_829_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_826_, v_fst_821_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_911_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_911_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_911_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_911_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_mkIntLE(v_a_828_, v_a_830_);
lean_inc(v_fst_821_);
lean_inc(v_fst_817_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 3);
lean_ctor_set(v___x_819_, 1, v_fst_821_);
v___x_836_ = v___x_819_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_fst_817_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_fst_821_);
v___x_836_ = v_reuseFailAlloc_910_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = l_Int_Internal_Linear_Expr_norm(v___x_836_);
lean_dec_ref(v___x_836_);
v___x_838_ = l_Int_Internal_Linear_Poly_isUnsatLe(v___x_837_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; 
v___x_839_ = l_Int_Internal_Linear_Poly_isValidLe(v___x_837_);
if (v___x_839_ == 0)
{
lean_del_object(v___x_824_);
lean_del_object(v___x_814_);
if (v___y_806_ == 0)
{
lean_del_object(v___x_832_);
v___y_749_ = v___f_826_;
v___y_750_ = v_snd_822_;
v___y_751_ = v_fst_817_;
v___y_752_ = v___x_834_;
v___y_753_ = v_fst_821_;
v___y_754_ = v___x_837_;
goto v___jp_748_;
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; 
lean_inc_ref(v___x_837_);
v___x_840_ = l_Int_Internal_Linear_Poly_toExpr(v___x_837_);
v___x_841_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_840_, v_fst_817_);
lean_dec_ref(v___x_840_);
if (v___x_841_ == 0)
{
lean_del_object(v___x_832_);
v___y_749_ = v___f_826_;
v___y_750_ = v_snd_822_;
v___y_751_ = v_fst_817_;
v___y_752_ = v___x_834_;
v___y_753_ = v_fst_821_;
v___y_754_ = v___x_837_;
goto v___jp_748_;
}
else
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28);
v___x_843_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_821_, v___x_842_);
if (v___x_843_ == 0)
{
lean_del_object(v___x_832_);
v___y_749_ = v___f_826_;
v___y_750_ = v_snd_822_;
v___y_751_ = v_fst_817_;
v___y_752_ = v___x_834_;
v___y_753_ = v_fst_821_;
v___y_754_ = v___x_837_;
goto v___jp_748_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec_ref(v___x_837_);
lean_dec_ref(v___x_834_);
lean_dec_ref(v___f_826_);
lean_dec(v_snd_822_);
lean_dec(v_fst_821_);
lean_dec(v_fst_817_);
v___x_844_ = lean_box(0);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_844_);
v___x_846_ = v___x_832_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v___x_837_);
lean_del_object(v___x_832_);
lean_dec_ref(v___f_826_);
v___x_848_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_849_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_822_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_870_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_870_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_870_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_870_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_854_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
v___x_855_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_817_);
v___x_856_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_821_);
v___x_857_ = l_Lean_eagerReflBoolTrue;
v___x_858_ = l_Lean_mkApp4(v___x_854_, v_a_850_, v___x_855_, v___x_856_, v___x_857_);
v___x_859_ = l_Lean_mkPropEq(v___x_834_, v___x_848_);
v___x_860_ = l_Lean_Meta_mkExpectedPropHint(v___x_858_, v___x_859_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_860_);
lean_ctor_set(v___x_824_, 0, v___x_848_);
v___x_862_ = v___x_824_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_869_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_862_);
v___x_864_ = v___x_814_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_864_);
v___x_866_ = v___x_852_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___x_834_);
lean_del_object(v___x_824_);
lean_dec(v_fst_821_);
lean_dec(v_fst_817_);
lean_del_object(v___x_814_);
v_a_871_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_849_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_849_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v___x_837_);
lean_del_object(v___x_832_);
lean_dec_ref(v___f_826_);
v___x_879_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3);
v___x_880_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_822_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_901_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_901_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_901_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_901_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_885_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
v___x_886_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_817_);
v___x_887_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_821_);
v___x_888_ = l_Lean_eagerReflBoolTrue;
v___x_889_ = l_Lean_mkApp4(v___x_885_, v_a_881_, v___x_886_, v___x_887_, v___x_888_);
v___x_890_ = l_Lean_mkPropEq(v___x_834_, v___x_879_);
v___x_891_ = l_Lean_Meta_mkExpectedPropHint(v___x_889_, v___x_890_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_891_);
lean_ctor_set(v___x_824_, 0, v___x_879_);
v___x_893_ = v___x_824_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_900_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_893_);
v___x_895_ = v___x_814_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_899_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_895_);
v___x_897_ = v___x_883_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v___x_834_);
lean_del_object(v___x_824_);
lean_dec(v_fst_821_);
lean_dec(v_fst_817_);
lean_del_object(v___x_814_);
v_a_902_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_880_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_880_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_a_828_);
lean_dec_ref(v___f_826_);
lean_del_object(v___x_824_);
lean_dec(v_snd_822_);
lean_dec(v_fst_821_);
lean_del_object(v___x_819_);
lean_dec(v_fst_817_);
lean_del_object(v___x_814_);
v_a_912_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_829_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_829_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v___f_826_);
lean_del_object(v___x_824_);
lean_dec(v_snd_822_);
lean_dec(v_fst_821_);
lean_del_object(v___x_819_);
lean_dec(v_fst_817_);
lean_del_object(v___x_814_);
v_a_920_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_827_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_827_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
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
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_933_; 
lean_dec(v_a_808_);
v___x_931_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_931_);
v___x_933_ = v___x_810_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
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
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_807_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_807_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* v_e_946_, lean_object* v_checkIfModified_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_checkIfModified_boxed_953_; lean_object* v_res_954_; 
v_checkIfModified_boxed_953_ = lean_unbox(v_checkIfModified_947_);
v_res_954_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_946_, v_checkIfModified_boxed_953_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_954_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_box(0);
v___x_961_ = l_Lean_Level_succ___override(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_box(0);
v___x_963_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
v___x_966_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
v___x_967_ = l_Lean_mkConst(v___x_966_, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_mkSort(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
v___x_989_ = l_Lean_mkIntLit(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
v___x_995_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20));
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(0);
v___x_1002_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23));
v___x_1003_ = l_Lean_mkConst(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26));
v___x_1010_ = l_Lean_mkConst(v___x_1009_, v___x_1008_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29));
v___x_1017_ = l_Lean_mkConst(v___x_1016_, v___x_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_val_1025_; lean_object* v_h_u2081_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8));
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = l_Lean_Expr_isAppOfArity(v_e_1018_, v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
uint8_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = 1;
v___x_1073_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_1018_, v___x_1072_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_Lean_Expr_appArg_x21(v_e_1018_);
v___x_1075_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1074_, v_a_1020_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = l_Lean_Expr_cleanupAnnotations(v_a_1076_);
lean_dec(v_a_1076_);
v___x_1078_ = l_Lean_Expr_isApp(v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1077_);
v___x_1080_ = l_Lean_Expr_isApp(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v___x_1079_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1079_);
v___x_1082_ = l_Lean_Expr_isApp(v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v___x_1081_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1081_);
lean_dec_ref(v___x_1081_);
v___x_1084_ = l_Lean_Expr_isApp(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v___x_1083_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v_arg_1085_; lean_object* v_arg_1086_; lean_object* v_arg_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_arg_1085_ = lean_ctor_get(v___x_1077_, 1);
lean_inc_ref(v_arg_1085_);
lean_dec_ref(v___x_1077_);
v_arg_1086_ = lean_ctor_get(v___x_1079_, 1);
lean_inc_ref(v_arg_1086_);
lean_dec_ref(v___x_1079_);
v_arg_1087_ = lean_ctor_get(v___x_1083_, 1);
lean_inc_ref(v_arg_1087_);
v___x_1088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1083_);
lean_dec_ref(v___x_1083_);
v___x_1089_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11));
v___x_1090_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14));
v___x_1092_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17));
v___x_1094_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_1096_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1095_);
lean_dec_ref(v___x_1088_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1087_, v_a_1020_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l_Lean_Expr_cleanupAnnotations(v_a_1098_);
lean_dec(v_a_1098_);
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16));
v___x_1101_ = l_Lean_Expr_isConstOf(v___x_1099_, v___x_1100_);
lean_dec_ref(v___x_1099_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1102_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1085_);
v___x_1103_ = l_Lean_mkIntAdd(v_arg_1085_, v___x_1102_);
lean_inc_ref(v_arg_1086_);
v___x_1104_ = l_Lean_mkIntLE(v___x_1103_, v_arg_1086_);
v___x_1105_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
v___x_1106_ = l_Lean_mkAppB(v___x_1105_, v_arg_1086_, v_arg_1085_);
v_val_1025_ = v___x_1104_;
v_h_u2081_1026_ = v___x_1106_;
v___y_1027_ = v_a_1019_;
v___y_1028_ = v_a_1020_;
v___y_1029_ = v_a_1021_;
v___y_1030_ = v_a_1022_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
v_a_1107_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1097_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1097_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v___x_1115_; 
lean_dec_ref(v___x_1088_);
v___x_1115_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1087_, v_a_1020_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = l_Lean_Expr_cleanupAnnotations(v_a_1116_);
lean_dec(v_a_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16));
v___x_1119_ = l_Lean_Expr_isConstOf(v___x_1117_, v___x_1118_);
lean_dec_ref(v___x_1117_);
if (v___x_1119_ == 0)
{
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1086_);
v___x_1121_ = l_Lean_mkIntAdd(v_arg_1086_, v___x_1120_);
lean_inc_ref(v_arg_1085_);
v___x_1122_ = l_Lean_mkIntLE(v___x_1121_, v_arg_1085_);
v___x_1123_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
v___x_1124_ = l_Lean_mkAppB(v___x_1123_, v_arg_1086_, v_arg_1085_);
v_val_1025_ = v___x_1122_;
v_h_u2081_1026_ = v___x_1124_;
v___y_1027_ = v_a_1019_;
v___y_1028_ = v_a_1020_;
v___y_1029_ = v_a_1021_;
v___y_1030_ = v_a_1022_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
v_a_1125_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1115_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1115_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_object* v___x_1133_; 
lean_dec_ref(v___x_1088_);
v___x_1133_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1087_, v_a_1020_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l_Lean_Expr_cleanupAnnotations(v_a_1134_);
lean_dec(v_a_1134_);
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16));
v___x_1137_ = l_Lean_Expr_isConstOf(v___x_1135_, v___x_1136_);
lean_dec_ref(v___x_1135_);
if (v___x_1137_ == 0)
{
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_inc_ref(v_arg_1086_);
lean_inc_ref(v_arg_1085_);
v___x_1138_ = l_Lean_mkIntLE(v_arg_1085_, v_arg_1086_);
v___x_1139_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
v___x_1140_ = l_Lean_mkAppB(v___x_1139_, v_arg_1086_, v_arg_1085_);
v_val_1025_ = v___x_1138_;
v_h_u2081_1026_ = v___x_1140_;
v___y_1027_ = v_a_1019_;
v___y_1028_ = v_a_1020_;
v___y_1029_ = v_a_1021_;
v___y_1030_ = v_a_1022_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
v_a_1141_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1133_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1133_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v___x_1088_);
v___x_1149_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1087_, v_a_1020_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Lean_Expr_cleanupAnnotations(v_a_1150_);
lean_dec(v_a_1150_);
v___x_1152_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16));
v___x_1153_ = l_Lean_Expr_isConstOf(v___x_1151_, v___x_1152_);
lean_dec_ref(v___x_1151_);
if (v___x_1153_ == 0)
{
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_inc_ref(v_arg_1085_);
lean_inc_ref(v_arg_1086_);
v___x_1154_ = l_Lean_mkIntLE(v_arg_1086_, v_arg_1085_);
v___x_1155_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
v___x_1156_ = l_Lean_mkAppB(v___x_1155_, v_arg_1086_, v_arg_1085_);
v_val_1025_ = v___x_1154_;
v_h_u2081_1026_ = v___x_1156_;
v___y_1027_ = v_a_1019_;
v___y_1028_ = v_a_1020_;
v___y_1029_ = v_a_1021_;
v___y_1030_ = v_a_1022_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1085_);
lean_dec_ref(v_e_1018_);
v_a_1157_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1149_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1149_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
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
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v_e_1018_);
v_a_1165_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1075_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1075_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
v___jp_1024_:
{
uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = 0;
lean_inc_ref(v_val_1025_);
v___x_1032_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_val_1025_, v___x_1031_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1065_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1065_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1065_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_a_1033_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1059_; 
v_val_1037_ = lean_ctor_get(v_a_1033_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1039_ = v_a_1033_;
v_isShared_1040_ = v_isSharedCheck_1059_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_val_1037_);
lean_dec(v_a_1033_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1059_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_fst_1041_; lean_object* v_snd_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1058_; 
v_fst_1041_ = lean_ctor_get(v_val_1037_, 0);
v_snd_1042_ = lean_ctor_get(v_val_1037_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_val_1037_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1044_ = v_val_1037_;
v_isShared_1045_ = v_isSharedCheck_1058_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_snd_1042_);
lean_inc(v_fst_1041_);
lean_dec(v_val_1037_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1058_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1046_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
v___x_1047_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
lean_inc(v_fst_1041_);
v___x_1048_ = l_Lean_mkApp6(v___x_1046_, v___x_1047_, v_e_1018_, v_val_1025_, v_fst_1041_, v_h_u2081_1026_, v_snd_1042_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_fst_1041_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1050_);
v___x_1052_ = v___x_1039_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1052_);
v___x_1054_ = v___x_1035_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_a_1033_);
lean_dec_ref(v_e_1018_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_val_1025_);
lean_ctor_set(v___x_1060_, 1, v_h_u2081_1026_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1061_);
v___x_1063_ = v___x_1035_;
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
lean_dec_ref(v_h_u2081_1026_);
lean_dec_ref(v_val_1025_);
lean_dec_ref(v_e_1018_);
return v___x_1032_;
}
}
v___jp_1066_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* v_e_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(v_e_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
return v_res_1179_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
v___x_1188_ = l_Lean_mkConst(v___x_1187_, v___x_1186_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(0);
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
v___x_1197_ = l_Lean_mkConst(v___x_1196_, v___x_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
v___x_1206_ = l_Lean_mkConst(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* v_e_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v_h_1216_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = l_Lean_instInhabitedExpr;
v___x_1235_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1402_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1402_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1402_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
if (lean_obj_tag(v_a_1236_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1397_; 
v_val_1240_ = lean_ctor_get(v_a_1236_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_a_1236_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1242_ = v_a_1236_;
v_isShared_1243_ = v_isSharedCheck_1397_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_val_1240_);
lean_dec(v_a_1236_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1397_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_snd_1244_; lean_object* v_fst_1245_; lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1396_; 
v_snd_1244_ = lean_ctor_get(v_val_1240_, 1);
lean_inc(v_snd_1244_);
v_fst_1245_ = lean_ctor_get(v_val_1240_, 0);
lean_inc(v_fst_1245_);
lean_dec(v_val_1240_);
v_fst_1246_ = lean_ctor_get(v_snd_1244_, 0);
v_snd_1247_ = lean_ctor_get(v_snd_1244_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_snd_1244_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1249_ = v_snd_1244_;
v_isShared_1250_ = v_isSharedCheck_1396_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_inc(v_fst_1246_);
lean_dec(v_snd_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1396_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; uint8_t v___x_1300_; 
v___x_1251_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
v___x_1300_ = lean_int_dec_eq(v_fst_1245_, v___x_1251_);
if (v___x_1300_ == 0)
{
lean_object* v___f_1301_; lean_object* v___x_1302_; 
lean_del_object(v___x_1238_);
lean_inc(v_snd_1247_);
v___f_1301_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1301_, 0, v___x_1234_);
lean_closure_set(v___f_1301_, 1, v_snd_1247_);
lean_inc(v_fst_1246_);
lean_inc_ref(v___f_1301_);
v___x_1302_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1301_, v_fst_1246_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1383_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1383_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1383_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___y_1308_; uint8_t v___x_1373_; 
v___x_1373_ = lean_int_dec_le(v___x_1251_, v_fst_1245_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1374_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_1375_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1377_ = lean_int_neg(v_fst_1245_);
v___x_1378_ = l_Int_toNat(v___x_1377_);
lean_dec(v___x_1377_);
v___x_1379_ = l_Lean_instToExprInt_mkNat(v___x_1378_);
v___x_1380_ = l_Lean_mkApp3(v___x_1374_, v___x_1375_, v___x_1376_, v___x_1379_);
v___y_1308_ = v___x_1380_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = l_Int_toNat(v_fst_1245_);
v___x_1382_ = l_Lean_instToExprInt_mkNat(v___x_1381_);
v___y_1308_ = v___x_1382_;
goto v___jp_1307_;
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
lean_inc_ref(v___y_1308_);
v___x_1309_ = l_Lean_mkIntDvd(v___y_1308_, v_a_1303_);
v___x_1310_ = l_Int_Internal_Linear_Expr_norm(v_fst_1246_);
lean_inc(v_fst_1245_);
v___x_1311_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v___x_1310_, v_fst_1245_);
v___x_1312_ = l_Int_Internal_Linear_Poly_getConst(v___x_1310_);
v___x_1313_ = lean_int_emod(v___x_1312_, v___x_1311_);
lean_dec(v___x_1312_);
v___x_1314_ = lean_int_dec_eq(v___x_1313_, v___x_1251_);
lean_dec(v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v___x_1311_);
lean_dec_ref(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec_ref(v___f_1301_);
lean_dec(v_fst_1245_);
v___x_1315_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3);
v___x_1316_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1247_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1336_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1336_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1336_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1321_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
v___x_1322_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1246_);
v___x_1323_ = l_Lean_eagerReflBoolTrue;
v___x_1324_ = l_Lean_mkApp4(v___x_1321_, v_a_1317_, v___y_1308_, v___x_1322_, v___x_1323_);
v___x_1325_ = l_Lean_mkPropEq(v___x_1309_, v___x_1315_);
v___x_1326_ = l_Lean_Meta_mkExpectedPropHint(v___x_1324_, v___x_1325_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1326_);
lean_ctor_set(v___x_1249_, 0, v___x_1315_);
v___x_1328_ = v___x_1249_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1328_);
v___x_1330_ = v___x_1242_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1330_);
v___x_1332_ = v___x_1319_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
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
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v___x_1309_);
lean_dec_ref(v___y_1308_);
lean_del_object(v___x_1249_);
lean_dec(v_fst_1246_);
lean_del_object(v___x_1242_);
v_a_1337_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1316_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1316_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
lean_del_object(v___x_1249_);
lean_del_object(v___x_1242_);
v___x_1345_ = l_Int_Internal_Linear_Poly_div(v___x_1311_, v___x_1310_);
lean_inc_ref(v___x_1345_);
v___x_1346_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1345_);
v___x_1347_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1246_, v___x_1346_);
lean_dec_ref(v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1305_);
v___x_1348_ = lean_int_ediv(v_fst_1245_, v___x_1311_);
lean_dec(v_fst_1245_);
lean_inc_ref(v___x_1345_);
v___x_1349_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1301_, v___x_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; uint8_t v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = lean_int_dec_le(v___x_1251_, v___x_1348_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1352_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_1354_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1355_ = lean_int_neg(v___x_1348_);
lean_dec(v___x_1348_);
v___x_1356_ = l_Int_toNat(v___x_1355_);
lean_dec(v___x_1355_);
v___x_1357_ = l_Lean_instToExprInt_mkNat(v___x_1356_);
v___x_1358_ = l_Lean_mkApp3(v___x_1352_, v___x_1353_, v___x_1354_, v___x_1357_);
v___y_1253_ = v___y_1308_;
v___y_1254_ = v___x_1311_;
v___y_1255_ = v_a_1350_;
v___y_1256_ = v___x_1345_;
v___y_1257_ = v___x_1309_;
v___y_1258_ = v___x_1358_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = l_Int_toNat(v___x_1348_);
lean_dec(v___x_1348_);
v___x_1360_ = l_Lean_instToExprInt_mkNat(v___x_1359_);
v___y_1253_ = v___y_1308_;
v___y_1254_ = v___x_1311_;
v___y_1255_ = v_a_1350_;
v___y_1256_ = v___x_1345_;
v___y_1257_ = v___x_1309_;
v___y_1258_ = v___x_1360_;
goto v___jp_1252_;
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v___x_1348_);
lean_dec_ref(v___x_1345_);
lean_dec(v___x_1311_);
lean_dec_ref(v___x_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_snd_1247_);
lean_dec(v_fst_1246_);
v_a_1361_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1349_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1349_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec_ref(v___x_1345_);
lean_dec(v___x_1311_);
lean_dec_ref(v___x_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v___f_1301_);
lean_dec(v_snd_1247_);
lean_dec(v_fst_1246_);
lean_dec(v_fst_1245_);
v___x_1369_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1369_);
v___x_1371_ = v___x_1305_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v___f_1301_);
lean_del_object(v___x_1249_);
lean_dec(v_snd_1247_);
lean_dec(v_fst_1246_);
lean_dec(v_fst_1245_);
lean_del_object(v___x_1242_);
v_a_1384_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1302_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1302_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_del_object(v___x_1249_);
lean_dec(v_snd_1247_);
lean_dec(v_fst_1246_);
lean_dec(v_fst_1245_);
lean_del_object(v___x_1242_);
v___x_1392_ = lean_box(0);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1392_);
v___x_1394_ = v___x_1238_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
v___jp_1252_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
lean_inc_ref(v___y_1258_);
v___x_1259_ = l_Lean_mkIntDvd(v___y_1258_, v___y_1255_);
v___x_1260_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
v___x_1261_ = lean_int_dec_eq(v___y_1254_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1247_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
v___x_1265_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1246_);
v___x_1266_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1256_);
v___x_1267_ = lean_int_dec_le(v___x_1251_, v___y_1254_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1268_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_1269_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_1270_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1271_ = lean_int_neg(v___y_1254_);
lean_dec(v___y_1254_);
v___x_1272_ = l_Int_toNat(v___x_1271_);
lean_dec(v___x_1271_);
v___x_1273_ = l_Lean_instToExprInt_mkNat(v___x_1272_);
v___x_1274_ = l_Lean_mkApp3(v___x_1268_, v___x_1269_, v___x_1270_, v___x_1273_);
v___y_1223_ = v___y_1258_;
v___y_1224_ = v___x_1259_;
v___y_1225_ = v___y_1253_;
v___y_1226_ = v___x_1264_;
v___y_1227_ = v_a_1263_;
v___y_1228_ = v___y_1257_;
v___y_1229_ = v___x_1266_;
v___y_1230_ = v___x_1265_;
v___y_1231_ = v___x_1274_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = l_Int_toNat(v___y_1254_);
lean_dec(v___y_1254_);
v___x_1276_ = l_Lean_instToExprInt_mkNat(v___x_1275_);
v___y_1223_ = v___y_1258_;
v___y_1224_ = v___x_1259_;
v___y_1225_ = v___y_1253_;
v___y_1226_ = v___x_1264_;
v___y_1227_ = v_a_1263_;
v___y_1228_ = v___y_1257_;
v___y_1229_ = v___x_1266_;
v___y_1230_ = v___x_1265_;
v___y_1231_ = v___x_1276_;
goto v___jp_1222_;
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v___x_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_fst_1246_);
v_a_1277_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1262_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1262_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1254_);
v___x_1285_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1247_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
v___x_1288_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1246_);
v___x_1289_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1256_);
v___x_1290_ = l_Lean_eagerReflBoolTrue;
v___x_1291_ = l_Lean_mkApp5(v___x_1287_, v_a_1286_, v___y_1253_, v___x_1288_, v___x_1289_, v___x_1290_);
v___y_1214_ = v___x_1259_;
v___y_1215_ = v___y_1257_;
v_h_1216_ = v___x_1291_;
goto v___jp_1213_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v___x_1259_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1253_);
lean_dec(v_fst_1246_);
v_a_1292_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1285_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1285_);
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
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_dec(v_a_1236_);
v___x_1398_ = lean_box(0);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1398_);
v___x_1400_ = v___x_1238_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
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
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1235_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1235_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
v___jp_1213_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_inc_ref(v___y_1214_);
v___x_1217_ = l_Lean_mkPropEq(v___y_1215_, v___y_1214_);
v___x_1218_ = l_Lean_Meta_mkExpectedPropHint(v_h_1216_, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1214_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1222_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_1226_);
v___x_1233_ = l_Lean_mkApp7(v___y_1226_, v___y_1227_, v___y_1225_, v___y_1230_, v___y_1223_, v___y_1229_, v___y_1231_, v___x_1232_);
v___y_1214_ = v___y_1224_;
v___y_1215_ = v___y_1228_;
v_h_1216_ = v___x_1233_;
goto v___jp_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* v_e_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(v_e_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1417_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
v___x_1428_ = l_Lean_mkConst(v___x_1427_, v___x_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* v_lhs_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = l_Lean_instInhabitedExpr;
v___x_1436_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_lhs_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1503_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1503_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1503_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_fst_1441_; lean_object* v_snd_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1502_; 
v_fst_1441_ = lean_ctor_get(v_a_1437_, 0);
v_snd_1442_ = lean_ctor_get(v_a_1437_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_a_1437_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1444_ = v_a_1437_;
v_isShared_1445_ = v_isSharedCheck_1502_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snd_1442_);
lean_inc(v_fst_1441_);
lean_dec(v_a_1437_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1502_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = l_Int_Internal_Linear_Expr_norm(v_fst_1441_);
lean_inc_ref(v___x_1446_);
v___x_1447_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1446_);
v___x_1448_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1441_, v___x_1447_);
lean_dec_ref(v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___f_1449_; lean_object* v___x_1450_; 
lean_del_object(v___x_1439_);
lean_inc(v_snd_1442_);
v___f_1449_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1449_, 0, v___x_1435_);
lean_closure_set(v___f_1449_, 1, v_snd_1442_);
v___x_1450_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1442_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
lean_inc(v_fst_1441_);
v___x_1453_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1441_);
lean_inc_ref(v___x_1446_);
v___x_1454_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1446_);
v___x_1455_ = l_Lean_eagerReflBoolTrue;
v___x_1456_ = l_Lean_mkApp4(v___x_1452_, v_a_1451_, v___x_1453_, v___x_1454_, v___x_1455_);
lean_inc_ref(v___f_1449_);
v___x_1457_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1449_, v_fst_1441_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1449_, v___x_1446_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1473_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1473_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1473_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_inc(v_a_1460_);
v___x_1464_ = l_Lean_mkIntEq(v_a_1458_, v_a_1460_);
v___x_1465_ = l_Lean_Meta_mkExpectedPropHint(v___x_1456_, v___x_1464_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1465_);
lean_ctor_set(v___x_1444_, 0, v_a_1460_);
v___x_1467_ = v___x_1444_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1460_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1468_);
v___x_1470_ = v___x_1462_;
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
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_a_1458_);
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1444_);
v_a_1474_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1459_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1459_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___x_1456_);
lean_dec_ref(v___f_1449_);
lean_dec_ref(v___x_1446_);
lean_del_object(v___x_1444_);
v_a_1482_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1457_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1457_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v___f_1449_);
lean_dec_ref(v___x_1446_);
lean_del_object(v___x_1444_);
lean_dec(v_fst_1441_);
v_a_1490_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1450_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1450_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec_ref(v___x_1446_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
v___x_1498_ = lean_box(0);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1498_);
v___x_1500_ = v___x_1439_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1436_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1436_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* v_lhs_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(v_lhs_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
return v_res_1518_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
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
