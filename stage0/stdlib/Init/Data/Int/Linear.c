// Lean compiler output
// Module: Init.Data.Int.Linear
// Imports: Init.ByCases Init.Data.Prod Init.Data.Int.Lemmas Init.Data.Int.LemmasAux Init.Data.Int.DivMod.Bootstrap Init.Data.Int.Cooper Init.Data.Int.Gcd Init.Data.RArray Init.Data.AC
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_not__le__of__le__cert___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__var__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__diseq__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__coeff__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__solve__combine__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_norm__dvd__gcd__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__split__dvd1__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst___boxed(lean_object*);
lean_object* l_Int_lcm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__var__const__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDiseq(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_unsatEqDivCoeffCert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_norm__eq__var__cert___closed__0;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__split__dvd1__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__of__eq__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__var__const__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDvd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__coeff__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__right__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__le__subst__nonpos__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__combine__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_abs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__neg__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__def__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__left__split__dvd__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__elim__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__coeff__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__coeff__cert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instBEqPoly___closed__0;
LEAN_EXPORT lean_object* l_Int_Linear_cooper__right__split__ineq__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__coeff__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__unsat__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__split__dvd2__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__of__le__ge__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__def_x27__cert___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__left__split__dvd__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_diseq__eq__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__elim__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_diseq__split__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_not__le__norm__expr__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__neg__le__tight__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnNum(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__split__dvd2__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_Expr_toPoly_x27___closed__0;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatEq___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_not__le__norm__expr__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divCoeffs(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__neg__cert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__left__split__ineq__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_emod__le__cert___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__combine__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__of__eq__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__neg__le__tight__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instInhabitedExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__split__dvd2__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__combine__coeff__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(lean_object*, lean_object*);
static lean_object* l_Int_Linear_Poly_denote_x27_go___closed__0;
static lean_object* l_Int_Linear_instBEqExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_emod__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidLe___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instBEqPoly;
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__split__ineq__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__le__tight__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__unsat__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divCoeffs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__right__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__combine__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__split__ineq__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_norm__le__coeff__tight__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__def__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatLe___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_diseq__eq__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cdiv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__split__ineq__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__solve__elim__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__le__subst__nonneg__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__right__split__dvd__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__le__subst__nonneg__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__left__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__of__le__ge__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__split__dvd1__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instBEqExpr;
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__split__dvd1__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631____boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__left__split__ineq__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__split__dvd2__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__unsat__coeff__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__eq__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__solve__elim__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__coeff__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__le__subst__nonpos__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__def_x27__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_cooper__right__split__ineq__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__coeff__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__var__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__of__core__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__of__core__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_abs(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_diseq__split__cert___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_dvd__le__tight__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__unsat__coeff__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_unsatEqDivCoeffCert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___closed__0;
LEAN_EXPORT uint8_t l_Int_Linear_norm__le__coeff__tight__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__diseq__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__split__ineq__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_norm__dvd__gcd__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__dvd__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__solve__combine__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnAdd___boxed(lean_object*, lean_object*);
static lean_object* l_Int_Linear_instInhabitedExpr___closed__1;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_not__le__of__le__cert(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__left__cert___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cooper__right__split__dvd__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__coeff__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__elim__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__combine__coeff__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_eq__eq__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_eq__dvd__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__combine__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDiseq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_dvd__elim__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Var_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instInhabitedExpr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_Linear_instInhabitedExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_int_dec_eq(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_nat_dec_eq(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_3 = x_20;
x_4 = x_21;
x_5 = x_22;
x_6 = x_23;
goto block_9;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_6 = x_29;
goto block_9;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_2, 0);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
return x_36;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_int_dec_eq(x_37, x_39);
if (x_41 == 0)
{
return x_41;
}
else
{
x_1 = x_38;
x_2 = x_40;
goto _start;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
return x_44;
}
}
default: 
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159_(x_45, x_47);
if (x_49 == 0)
{
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_int_dec_eq(x_46, x_48);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(0);
x_52 = lean_unbox(x_51);
return x_52;
}
}
}
block_9:
{
uint8_t x_7; 
x_7 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159_(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Int_Linear_instBEqExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_159____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_Linear_instBEqExpr___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_RArray_getImpl___redArg(x_1, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Int_Linear_Expr_denote(x_1, x_6);
x_9 = l_Int_Linear_Expr_denote(x_1, x_7);
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Int_Linear_Expr_denote(x_1, x_11);
x_14 = l_Int_Linear_Expr_denote(x_1, x_12);
x_15 = lean_int_sub(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = l_Int_Linear_Expr_denote(x_1, x_16);
x_18 = lean_int_neg(x_17);
lean_dec(x_17);
return x_18;
}
case 5:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = l_Int_Linear_Expr_denote(x_1, x_20);
x_22 = lean_int_mul(x_19, x_21);
lean_dec(x_21);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Int_Linear_Expr_denote(x_1, x_23);
x_26 = lean_int_mul(x_25, x_24);
lean_dec(x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_dec_eq(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_int_dec_eq(x_10, x_13);
if (x_16 == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_11, x_14);
if (x_17 == 0)
{
return x_17;
}
else
{
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Int_Linear_instBEqPoly___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instBEqPoly() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_Linear_instBEqPoly___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_RArray_getImpl___redArg(x_1, x_5);
x_8 = lean_int_mul(x_4, x_7);
lean_dec(x_7);
x_9 = l_Int_Linear_Poly_denote(x_1, x_6);
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_Poly_denote_x27_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_int_add(x_2, x_4);
lean_dec(x_2);
return x_7;
}
else
{
return x_2;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_12 = lean_int_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_RArray_getImpl___redArg(x_1, x_9);
x_14 = lean_int_mul(x_8, x_13);
lean_dec(x_13);
x_15 = lean_int_add(x_2, x_14);
lean_dec(x_14);
lean_dec(x_2);
x_2 = x_15;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_RArray_getImpl___redArg(x_1, x_9);
x_18 = lean_int_add(x_2, x_17);
lean_dec(x_17);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_Linear_Poly_denote_x27_go(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_8 = lean_int_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_RArray_getImpl___redArg(x_1, x_5);
x_10 = lean_int_mul(x_4, x_9);
lean_dec(x_9);
x_11 = l_Int_Linear_Poly_denote_x27_go(x_1, x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_RArray_getImpl___redArg(x_1, x_5);
x_13 = l_Int_Linear_Poly_denote_x27_go(x_1, x_12, x_6);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_denote_x27(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Int_Linear_instInhabitedExpr___closed__0;
x_8 = lean_int_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_apply_2(x_3, x_6, lean_box(0));
return x_9;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___closed__0;
x_14 = lean_int_dec_eq(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_apply_4(x_5, x_10, x_11, x_12, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_5);
x_16 = lean_apply_2(x_4, x_11, x_12);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg___closed__0;
x_11 = lean_int_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_4(x_4, x_7, x_8, x_9, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_4);
x_13 = lean_apply_2(x_3, x_8, x_9);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_int_add(x_2, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_int_add(x_2, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_Int_Linear_Poly_addConst(x_10, x_2);
lean_ctor_set(x_1, 2, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = l_Int_Linear_Poly_addConst(x_14, x_2);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_addConst(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = l_Nat_blt(x_6, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_nat_dec_eq(x_2, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Int_Linear_Poly_insert(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_15 = lean_int_add(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_16 = l_Int_Linear_instInhabitedExpr___closed__0;
x_17 = lean_int_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_dec(x_15);
lean_free_object(x_3);
lean_dec(x_6);
return x_7;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = lean_nat_dec_eq(x_2, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Int_Linear_Poly_insert(x_1, x_2, x_7);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_21 = lean_int_add(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_22 = l_Int_Linear_instInhabitedExpr___closed__0;
x_23 = lean_int_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
return x_24;
}
else
{
lean_dec(x_21);
lean_dec(x_6);
return x_7;
}
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_3);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_norm(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Int_Linear_Poly_norm(x_4);
x_6 = l_Int_Linear_Poly_insert(x_2, x_3, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_append(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Int_Linear_Poly_addConst(x_2, x_3);
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Int_Linear_Poly_append(x_6, x_2);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Int_Linear_Poly_append(x_10, x_2);
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Int_Linear_Poly_append(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_int_add(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_int_add(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 2);
x_18 = l_Int_Linear_Poly_combine_x27(x_8, x_2, x_17);
lean_ctor_set(x_3, 2, x_18);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_22 = l_Int_Linear_Poly_combine_x27(x_8, x_2, x_21);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Int_Linear_Poly_combine_x27(x_8, x_25, x_3);
lean_ctor_set(x_2, 2, x_26);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_30 = l_Int_Linear_Poly_combine_x27(x_8, x_29, x_3);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_nat_dec_eq(x_33, x_36);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Nat_blt(x_36, x_33);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_3, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_3, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_3, 0);
lean_dec(x_43);
x_44 = l_Int_Linear_Poly_combine_x27(x_8, x_2, x_37);
lean_ctor_set(x_3, 2, x_44);
return x_3;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = l_Int_Linear_Poly_combine_x27(x_8, x_2, x_37);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 2, x_45);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_2);
lean_inc(x_3);
x_47 = l_Int_Linear_Poly_combine_x27(x_8, x_34, x_3);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_3, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_3, 0);
lean_dec(x_51);
lean_ctor_set(x_3, 2, x_47);
lean_ctor_set(x_3, 1, x_33);
lean_ctor_set(x_3, 0, x_32);
return x_3;
}
else
{
lean_object* x_52; 
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_33);
lean_ctor_set(x_52, 2, x_47);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_36);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_3);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_3, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_3, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_3, 0);
lean_dec(x_56);
x_57 = lean_int_add(x_32, x_35);
lean_dec(x_35);
lean_dec(x_32);
x_58 = l_Int_Linear_instInhabitedExpr___closed__0;
x_59 = lean_int_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Int_Linear_Poly_combine_x27(x_8, x_34, x_37);
lean_ctor_set(x_3, 2, x_60);
lean_ctor_set(x_3, 1, x_33);
lean_ctor_set(x_3, 0, x_57);
return x_3;
}
else
{
lean_dec(x_57);
lean_free_object(x_3);
lean_dec(x_33);
x_1 = x_8;
x_2 = x_34;
x_3 = x_37;
goto _start;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_3);
x_62 = lean_int_add(x_32, x_35);
lean_dec(x_35);
lean_dec(x_32);
x_63 = l_Int_Linear_instInhabitedExpr___closed__0;
x_64 = lean_int_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_Linear_Poly_combine_x27(x_8, x_34, x_37);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_33);
lean_ctor_set(x_66, 2, x_65);
return x_66;
}
else
{
lean_dec(x_62);
lean_dec(x_33);
x_1 = x_8;
x_2 = x_34;
x_3 = x_37;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(100000000u);
x_4 = l_Int_Linear_Poly_combine_x27(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_int_mul(x_1, x_4);
lean_dec(x_1);
x_8 = l_Int_Linear_Poly_addConst(x_3, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_1);
return x_3;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_3);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_13 = l_Int_Linear_Expr_toPoly_x27_go(x_1, x_12, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_int_neg(x_1);
x_18 = l_Int_Linear_Expr_toPoly_x27_go(x_17, x_16, x_3);
x_2 = x_15;
x_3 = x_18;
goto _start;
}
case 4:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_int_neg(x_1);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_20;
goto _start;
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Int_Linear_instInhabitedExpr___closed__0;
x_26 = lean_int_dec_eq(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_int_mul(x_1, x_23);
lean_dec(x_1);
x_1 = x_27;
x_2 = x_24;
goto _start;
}
else
{
lean_dec(x_1);
return x_3;
}
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = l_Int_Linear_instInhabitedExpr___closed__0;
x_32 = lean_int_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_int_mul(x_1, x_30);
lean_dec(x_1);
x_1 = x_33;
x_2 = x_29;
goto _start;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_Linear_Expr_toPoly_x27_go(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Int_Linear_Expr_toPoly_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instInhabitedExpr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_3 = l_Int_Linear_Expr_toPoly_x27___closed__0;
x_4 = l_Int_Linear_Expr_toPoly_x27_go(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Expr_toPoly_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Int_Linear_Expr_toPoly_x27(x_1);
x_3 = l_Int_Linear_Poly_norm(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Expr_norm(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cdiv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_int_neg(x_1);
x_4 = lean_int_ediv(x_3, x_2);
lean_dec(x_3);
x_5 = lean_int_neg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cdiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_cdiv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cmod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_int_neg(x_1);
x_4 = lean_int_emod(x_3, x_2);
lean_dec(x_3);
x_5 = lean_int_neg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cmod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_cmod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
x_1 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_getConst(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Int_Linear_cdiv(x_4, x_1);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Int_Linear_cdiv(x_6, x_1);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_int_ediv(x_10, x_1);
lean_dec(x_10);
x_13 = l_Int_Linear_Poly_div(x_1, x_11);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_17 = lean_int_ediv(x_14, x_1);
lean_dec(x_14);
x_18 = l_Int_Linear_Poly_div(x_1, x_16);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_div(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divAll(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_int_emod(x_3, x_1);
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_int_emod(x_7, x_1);
x_10 = l_Int_Linear_instInhabitedExpr___closed__0;
x_11 = lean_int_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
return x_11;
}
else
{
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_Poly_divAll(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divCoeffs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_int_emod(x_5, x_1);
x_8 = l_Int_Linear_instInhabitedExpr___closed__0;
x_9 = lean_int_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
return x_9;
}
else
{
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divCoeffs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_Poly_divCoeffs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_int_mul(x_2, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_int_mul(x_2, x_10);
lean_dec(x_10);
x_13 = l_Int_Linear_Poly_mul_x27(x_11, x_2);
lean_ctor_set(x_1, 2, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_int_mul(x_2, x_14);
lean_dec(x_14);
x_18 = l_Int_Linear_Poly_mul_x27(x_16, x_2);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_mul_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Int_Linear_Poly_mul_x27(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Int_Linear_Expr_toPoly_x27___closed__0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_mul(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_4(x_4, x_10, x_11, x_12, x_13);
return x_14;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_4(x_5, x_15, x_16, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_apply_6(x_6, x_20, x_21, x_22, x_23, x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_5, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_2, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_3, x_16, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_1(x_4, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_2(x_7, x_21, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_2(x_8, x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_3, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_4, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_5, x_16, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_1(x_8, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_2(x_6, x_21, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_2(x_7, x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Int_Linear_Expr_norm(x_4);
lean_dec(x_4);
x_6 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_norm__eq__cert(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Int_Linear_norm__eq__var__cert___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__var__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Int_Linear_Expr_norm(x_5);
lean_dec(x_5);
x_7 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_8 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_9 = l_Int_Linear_Expr_toPoly_x27___closed__0;
x_10 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__var__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_norm__eq__var__cert(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__var__const__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Int_Linear_Expr_norm(x_5);
lean_dec(x_5);
x_7 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_8 = lean_int_neg(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__var__const__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_norm__eq__var__const__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_norm__eq__coeff__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Int_Linear_Expr_norm(x_5);
lean_dec(x_5);
x_7 = l_Int_Linear_Poly_mul(x_3, x_4);
x_8 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Int_Linear_instInhabitedExpr___closed__0;
x_10 = lean_int_dec_lt(x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_norm__eq__coeff__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_norm__eq__coeff__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_norm__le__coeff__tight__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Int_Linear_Expr_norm(x_7);
lean_dec(x_7);
x_9 = l_Int_Linear_Poly_divCoeffs(x_4, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Int_Linear_Poly_div(x_4, x_8);
x_11 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_10);
lean_dec(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_norm__le__coeff__tight__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_norm__le__coeff__tight__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_Linear_Poly_isUnsatEq(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidEq(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_eq(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_Linear_Poly_isValidEq(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_lt(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatLe___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_Linear_Poly_isUnsatLe(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidLe(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_le(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidLe___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_Linear_Poly_isValidLe(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_unsatEqDivCoeffCert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_4 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Int_Linear_Expr_norm(x_4);
lean_dec(x_4);
x_12 = l_Int_Linear_Poly_divCoeffs(x_3, x_5);
if (x_12 == 0)
{
x_6 = x_12;
goto block_11;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Int_Linear_instInhabitedExpr___closed__0;
x_14 = lean_int_dec_lt(x_13, x_3);
x_6 = x_14;
goto block_11;
}
block_11:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Int_Linear_Poly_getConst(x_5);
lean_dec(x_5);
x_8 = l_Int_Linear_cmod(x_7, x_3);
lean_dec(x_7);
x_9 = l_Int_Linear_instInhabitedExpr___closed__0;
x_10 = lean_int_dec_lt(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_unsatEqDivCoeffCert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_unsatEqDivCoeffCert(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Int_gcd(x_1, x_2);
x_4 = lean_nat_to_int(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Int_gcd(x_3, x_2);
lean_dec(x_2);
x_6 = lean_nat_to_int(x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_gcdCoeffs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_4(x_4, x_7, x_8, x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Int_Linear_Poly_getConst(x_2);
x_4 = l_Int_Linear_Poly_gcdCoeffs(x_2, x_1);
x_5 = lean_int_emod(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDvd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_Poly_isUnsatDvd(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__coeff__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_int_mul(x_5, x_3);
x_9 = lean_int_dec_eq(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Int_Linear_Poly_mul(x_4, x_5);
x_11 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__coeff__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_dvd__coeff__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_norm__dvd__gcd__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_Expr_norm(x_2);
x_7 = l_Int_Linear_dvd__coeff__cert(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_norm__dvd__gcd__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_norm__dvd__gcd__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__elim__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 2);
x_9 = l_Int_gcd(x_1, x_7);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_dec_eq(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_8);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__elim__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_dvd__elim__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__elim__cert_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_3, x_1, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__elim__cert_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__elim__cert_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__solve__combine__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_nat_dec_eq(x_15, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_int_mul(x_8, x_14);
lean_dec(x_14);
x_23 = lean_int_mul(x_22, x_3);
lean_dec(x_22);
x_24 = lean_int_mul(x_9, x_18);
lean_dec(x_18);
x_25 = lean_int_mul(x_24, x_1);
lean_dec(x_24);
x_26 = lean_int_add(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
x_27 = lean_int_dec_eq(x_7, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_int_mul(x_1, x_3);
x_29 = lean_int_dec_eq(x_5, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_int_mul(x_8, x_3);
x_31 = l_Int_Linear_Poly_mul(x_16, x_30);
lean_dec(x_30);
x_32 = lean_int_mul(x_9, x_1);
x_33 = l_Int_Linear_Poly_mul(x_20, x_32);
lean_dec(x_32);
x_34 = l_Int_Linear_Poly_combine(x_31, x_33);
lean_ctor_set(x_4, 2, x_34);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_7);
x_35 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_4);
lean_dec(x_4);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_39 = lean_nat_dec_eq(x_15, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_int_mul(x_8, x_14);
lean_dec(x_14);
x_41 = lean_int_mul(x_40, x_3);
lean_dec(x_40);
x_42 = lean_int_mul(x_9, x_36);
lean_dec(x_36);
x_43 = lean_int_mul(x_42, x_1);
lean_dec(x_42);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = lean_int_dec_eq(x_7, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_int_mul(x_1, x_3);
x_47 = lean_int_dec_eq(x_5, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_int_mul(x_8, x_3);
x_49 = l_Int_Linear_Poly_mul(x_16, x_48);
lean_dec(x_48);
x_50 = lean_int_mul(x_9, x_1);
x_51 = l_Int_Linear_Poly_mul(x_38, x_50);
lean_dec(x_50);
x_52 = l_Int_Linear_Poly_combine(x_49, x_51);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_7);
lean_ctor_set(x_53, 1, x_15);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_53);
lean_dec(x_53);
return x_54;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__solve__combine__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = l_Int_Linear_dvd__solve__combine__cert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__combine__cert_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_6(x_3, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__combine__cert_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__combine__cert_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__solve__elim__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_nat_dec_eq(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_int_mul(x_11, x_3);
x_19 = lean_int_mul(x_14, x_1);
x_20 = l_Int_gcd(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_dec_eq(x_5, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Int_Linear_Poly_mul(x_13, x_14);
lean_dec(x_14);
x_24 = lean_int_neg(x_11);
lean_dec(x_11);
x_25 = l_Int_Linear_Poly_mul(x_16, x_24);
lean_dec(x_24);
x_26 = l_Int_Linear_Poly_combine(x_23, x_25);
x_27 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_26);
lean_dec(x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__solve__elim__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Int_Linear_dvd__solve__elim__cert(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__coeff__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_Linear_instInhabitedExpr___closed__0;
x_5 = lean_int_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l_Int_Linear_Poly_divCoeffs(x_3, x_1);
if (x_6 == 0)
{
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Int_Linear_Poly_div(x_3, x_1);
x_8 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__coeff__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_le__coeff__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__neg__cert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_4 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_5 = l_Int_Linear_Poly_mul(x_1, x_4);
x_6 = l_Int_Linear_Poly_addConst(x_5, x_3);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__neg__cert___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_le__neg__cert(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_denote_x27_go___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__combine__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Int_Linear_Poly_leadCoeff(x_1);
x_5 = lean_nat_abs(x_4);
lean_dec(x_4);
x_6 = l_Int_Linear_Poly_leadCoeff(x_2);
x_7 = lean_nat_abs(x_6);
lean_dec(x_6);
x_8 = lean_nat_to_int(x_7);
x_9 = l_Int_Linear_Poly_mul(x_1, x_8);
lean_dec(x_8);
x_10 = lean_nat_to_int(x_5);
x_11 = l_Int_Linear_Poly_mul(x_2, x_10);
lean_dec(x_10);
x_12 = l_Int_Linear_Poly_combine(x_9, x_11);
x_13 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_12);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__combine__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_le__combine__cert(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__combine__coeff__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = l_Int_Linear_Poly_leadCoeff(x_1);
x_8 = lean_nat_abs(x_7);
lean_dec(x_7);
x_9 = l_Int_Linear_Poly_leadCoeff(x_2);
x_10 = lean_nat_abs(x_9);
lean_dec(x_9);
x_11 = lean_nat_to_int(x_10);
x_12 = l_Int_Linear_Poly_mul(x_1, x_11);
lean_dec(x_11);
x_13 = lean_nat_to_int(x_8);
x_14 = l_Int_Linear_Poly_mul(x_2, x_13);
lean_dec(x_13);
x_15 = l_Int_Linear_Poly_combine(x_12, x_14);
x_16 = l_Int_Linear_Poly_divCoeffs(x_4, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Int_Linear_Poly_div(x_4, x_15);
x_18 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_17);
lean_dec(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__combine__coeff__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_le__combine__coeff__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__coeff__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_Linear_Poly_mul(x_2, x_3);
x_5 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_lt(x_6, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__coeff__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_eq__coeff__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__unsat__coeff__cert(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; 
x_9 = l_Int_Linear_Poly_divCoeffs(x_2, x_1);
if (x_9 == 0)
{
x_3 = x_9;
goto block_8;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Int_Linear_instInhabitedExpr___closed__0;
x_11 = lean_int_dec_lt(x_10, x_2);
x_3 = x_11;
goto block_8;
}
block_8:
{
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Int_Linear_Poly_getConst(x_1);
x_5 = l_Int_Linear_cmod(x_4, x_2);
lean_dec(x_4);
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_lt(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__unsat__coeff__cert___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_eq__unsat__coeff__cert(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_dec_eq(x_2, x_5);
if (x_7 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_coeff(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_abs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_abs(x_1);
x_3 = lean_nat_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_abs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_abs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__of__eq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Int_Linear_Poly_coeff(x_2, x_1);
x_6 = l_Int_Linear_abs(x_5);
x_7 = lean_int_dec_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_int_neg(x_5);
lean_dec(x_5);
x_9 = l_Int_Linear_Poly_insert(x_8, x_1, x_2);
x_10 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_9);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__of__eq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_dvd__of__eq__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__dvd__subst__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Int_Linear_Poly_coeff(x_2, x_1);
x_8 = lean_int_mul(x_7, x_3);
x_9 = l_Int_Linear_abs(x_8);
lean_dec(x_8);
x_10 = lean_int_dec_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = l_Int_Linear_Poly_coeff(x_4, x_1);
x_12 = lean_int_neg(x_7);
lean_inc(x_1);
x_13 = l_Int_Linear_Poly_insert(x_12, x_1, x_2);
x_14 = lean_int_neg(x_11);
lean_dec(x_11);
lean_inc(x_14);
x_15 = l_Int_Linear_Poly_insert(x_14, x_1, x_4);
x_16 = l_Int_Linear_Poly_mul(x_15, x_7);
lean_dec(x_7);
x_17 = l_Int_Linear_Poly_mul(x_13, x_14);
lean_dec(x_14);
x_18 = l_Int_Linear_Poly_combine(x_16, x_17);
x_19 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_18);
lean_dec(x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__dvd__subst__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Int_Linear_eq__dvd__subst__cert(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__eq__subst__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Int_Linear_Poly_coeff(x_2, x_1);
x_6 = l_Int_Linear_Poly_coeff(x_3, x_1);
x_7 = l_Int_Linear_Poly_mul(x_2, x_6);
lean_dec(x_6);
x_8 = lean_int_neg(x_5);
lean_dec(x_5);
x_9 = l_Int_Linear_Poly_mul(x_3, x_8);
lean_dec(x_8);
x_10 = l_Int_Linear_Poly_combine(x_7, x_9);
x_11 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__eq__subst__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_eq__eq__subst__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__le__subst__nonneg__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Int_Linear_Poly_coeff(x_2, x_1);
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Int_Linear_Poly_coeff(x_3, x_1);
x_9 = l_Int_Linear_Poly_mul(x_3, x_5);
lean_dec(x_5);
x_10 = lean_int_neg(x_8);
lean_dec(x_8);
x_11 = l_Int_Linear_Poly_mul(x_2, x_10);
lean_dec(x_10);
x_12 = l_Int_Linear_Poly_combine(x_9, x_11);
x_13 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_12);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__le__subst__nonneg__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_eq__le__subst__nonneg__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__le__subst__nonpos__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Int_Linear_Poly_coeff(x_2, x_1);
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Int_Linear_Poly_coeff(x_3, x_1);
x_9 = l_Int_Linear_Poly_mul(x_2, x_8);
lean_dec(x_8);
x_10 = lean_int_neg(x_5);
lean_dec(x_5);
x_11 = l_Int_Linear_Poly_mul(x_3, x_10);
lean_dec(x_10);
x_12 = l_Int_Linear_Poly_combine(x_9, x_11);
x_13 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_12);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__le__subst__nonpos__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_eq__le__subst__nonpos__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__of__core__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_5 = l_Int_Linear_Poly_mul(x_2, x_4);
x_6 = l_Int_Linear_Poly_combine(x_1, x_5);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__of__core__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_eq__of__core__cert(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDiseq(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_eq(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDiseq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_Linear_Poly_isUnsatDiseq(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_2(x_3, x_1, lean_box(0));
return x_7;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_8; 
x_8 = lean_apply_2(x_3, x_1, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatDiseq_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_diseq__eq__subst__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Int_Linear_Poly_coeff(x_2, x_1);
x_6 = l_Int_Linear_instInhabitedExpr___closed__0;
x_7 = lean_int_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Int_Linear_Poly_coeff(x_3, x_1);
x_9 = l_Int_Linear_Poly_mul(x_2, x_8);
lean_dec(x_8);
x_10 = lean_int_neg(x_5);
lean_dec(x_5);
x_11 = l_Int_Linear_Poly_mul(x_3, x_10);
lean_dec(x_10);
x_12 = l_Int_Linear_Poly_combine(x_9, x_11);
x_13 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_12);
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_diseq__eq__subst__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_diseq__eq__subst__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__of__le__ge__cert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_4 = l_Int_Linear_Poly_mul(x_1, x_3);
x_5 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__of__le__ge__cert___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_eq__of__le__ge__cert(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__diseq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_9; 
x_9 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Int_Linear_norm__eq__var__cert___closed__0;
lean_inc(x_1);
x_11 = l_Int_Linear_Poly_mul(x_1, x_10);
x_12 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_11);
lean_dec(x_11);
x_4 = x_12;
goto block_8;
}
else
{
x_4 = x_9;
goto block_8;
}
block_8:
{
if (x_4 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_6 = l_Int_Linear_Poly_addConst(x_1, x_5);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__diseq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_le__of__le__diseq__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_diseq__split__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Int_Linear_Poly_denote_x27_go___closed__0;
lean_inc(x_1);
x_5 = l_Int_Linear_Poly_addConst(x_1, x_4);
x_6 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_8 = l_Int_Linear_Poly_mul(x_1, x_7);
x_9 = l_Int_Linear_Poly_addConst(x_8, x_4);
x_10 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_9);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_diseq__split__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_diseq__split__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_nat_dec_eq(x_13, x_15);
if (x_18 == 0)
{
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_13, x_17);
if (x_19 == 0)
{
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Int_Linear_instInhabitedExpr___closed__0;
x_21 = lean_int_dec_lt(x_12, x_20);
if (x_21 == 0)
{
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_int_dec_lt(x_20, x_14);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_int_dec_lt(x_20, x_4);
if (x_23 == 0)
{
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_int_mul(x_12, x_4);
x_25 = l_Int_gcd(x_24, x_16);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_ediv(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Int_lcm(x_12, x_27);
lean_dec(x_27);
x_29 = lean_nat_dec_eq(x_5, x_28);
lean_dec(x_28);
return x_29;
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
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_cooper__dvd__left__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_tail(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__split__ineq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_19; 
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
x_19 = x_1;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_19 = x_22;
goto block_21;
}
block_18:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Int_Linear_Poly_leadCoeff(x_2);
lean_dec(x_2);
x_9 = lean_int_dec_eq(x_8, x_4);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
x_11 = l_Int_Linear_Poly_mul(x_6, x_4);
x_12 = lean_int_neg(x_10);
lean_dec(x_10);
x_13 = l_Int_Linear_Poly_mul(x_7, x_12);
lean_dec(x_12);
x_14 = l_Int_Linear_Poly_combine(x_11, x_13);
x_15 = lean_int_mul(x_4, x_3);
x_16 = l_Int_Linear_Poly_addConst(x_14, x_15);
lean_dec(x_15);
x_17 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_5, x_16);
lean_dec(x_16);
return x_17;
}
}
block_21:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_2);
x_6 = x_19;
x_7 = x_2;
goto block_18;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_6 = x_19;
x_7 = x_20;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__split__ineq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_cooper__dvd__left__split__ineq__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__split__dvd1__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; 
x_9 = l_Int_Linear_Poly_leadCoeff(x_1);
x_10 = lean_int_dec_eq(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
x_5 = x_1;
goto block_8;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_5 = x_11;
goto block_8;
}
}
block_8:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_Poly_addConst(x_5, x_4);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__split__dvd1__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_cooper__dvd__left__split__dvd1__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__left__split__dvd2__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_22; 
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
x_22 = x_1;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_22 = x_25;
goto block_24;
}
block_21:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
x_10 = lean_int_mul(x_9, x_3);
x_11 = lean_int_dec_eq(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = l_Int_Linear_Poly_leadCoeff(x_2);
lean_dec(x_2);
x_13 = l_Int_Linear_Poly_mul(x_7, x_12);
x_14 = lean_int_neg(x_9);
lean_dec(x_9);
x_15 = l_Int_Linear_Poly_mul(x_8, x_14);
lean_dec(x_14);
x_16 = l_Int_Linear_Poly_combine(x_13, x_15);
x_17 = lean_nat_to_int(x_4);
x_18 = lean_int_mul(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_19 = l_Int_Linear_Poly_addConst(x_16, x_18);
lean_dec(x_18);
x_20 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_19);
lean_dec(x_19);
return x_20;
}
}
block_24:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_2);
x_7 = x_22;
x_8 = x_2;
goto block_21;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_7 = x_22;
x_8 = x_23;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__left__split__dvd2__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Int_Linear_cooper__dvd__left__split__dvd2__cert(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__left__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_eq(x_9, x_11);
if (x_12 == 0)
{
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Int_Linear_instInhabitedExpr___closed__0;
x_14 = lean_int_dec_lt(x_8, x_13);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_int_dec_lt(x_13, x_10);
if (x_15 == 0)
{
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_abs(x_8);
x_17 = lean_nat_dec_eq(x_3, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__left__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_cooper__left__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__left__split__ineq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_19; 
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
x_19 = x_1;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_19 = x_22;
goto block_21;
}
block_18:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Int_Linear_Poly_leadCoeff(x_2);
lean_dec(x_2);
x_9 = lean_int_dec_eq(x_8, x_4);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
x_11 = l_Int_Linear_Poly_mul(x_6, x_4);
x_12 = lean_int_neg(x_10);
lean_dec(x_10);
x_13 = l_Int_Linear_Poly_mul(x_7, x_12);
lean_dec(x_12);
x_14 = l_Int_Linear_Poly_combine(x_11, x_13);
x_15 = lean_int_mul(x_4, x_3);
x_16 = l_Int_Linear_Poly_addConst(x_14, x_15);
lean_dec(x_15);
x_17 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_5, x_16);
lean_dec(x_16);
return x_17;
}
}
block_21:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_2);
x_6 = x_19;
x_7 = x_2;
goto block_18;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_6 = x_19;
x_7 = x_20;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__left__split__ineq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_cooper__left__split__ineq__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__left__split__dvd__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; 
x_9 = l_Int_Linear_Poly_leadCoeff(x_1);
x_10 = lean_int_dec_eq(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
x_5 = x_1;
goto block_8;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_5 = x_11;
goto block_8;
}
}
block_8:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_Poly_addConst(x_5, x_4);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__left__split__dvd__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_cooper__left__split__dvd__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_nat_dec_eq(x_13, x_15);
if (x_18 == 0)
{
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_13, x_17);
if (x_19 == 0)
{
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Int_Linear_instInhabitedExpr___closed__0;
x_21 = lean_int_dec_lt(x_12, x_20);
if (x_21 == 0)
{
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_int_dec_lt(x_20, x_14);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_int_dec_lt(x_20, x_4);
if (x_23 == 0)
{
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_int_mul(x_14, x_4);
x_25 = l_Int_gcd(x_24, x_16);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_ediv(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Int_lcm(x_14, x_27);
lean_dec(x_27);
x_29 = lean_nat_dec_eq(x_5, x_28);
lean_dec(x_28);
return x_29;
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
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_cooper__dvd__right__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__split__ineq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_19; 
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
x_19 = x_1;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_19 = x_22;
goto block_21;
}
block_18:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
x_9 = lean_int_dec_eq(x_8, x_4);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l_Int_Linear_Poly_leadCoeff(x_2);
lean_dec(x_2);
x_11 = l_Int_Linear_Poly_mul(x_6, x_10);
lean_dec(x_10);
x_12 = lean_int_neg(x_4);
x_13 = l_Int_Linear_Poly_mul(x_7, x_12);
x_14 = l_Int_Linear_Poly_combine(x_11, x_13);
x_15 = lean_int_mul(x_12, x_3);
lean_dec(x_12);
x_16 = l_Int_Linear_Poly_addConst(x_14, x_15);
lean_dec(x_15);
x_17 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_5, x_16);
lean_dec(x_16);
return x_17;
}
}
block_21:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_2);
x_6 = x_19;
x_7 = x_2;
goto block_18;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_6 = x_19;
x_7 = x_20;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__split__ineq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_cooper__dvd__right__split__ineq__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__split__dvd1__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; 
x_9 = l_Int_Linear_Poly_leadCoeff(x_1);
x_10 = lean_int_dec_eq(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
x_5 = x_1;
goto block_8;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_5 = x_11;
goto block_8;
}
}
block_8:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_Poly_addConst(x_5, x_4);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__split__dvd1__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_cooper__dvd__right__split__dvd1__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__dvd__right__split__dvd2__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_22; 
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
x_22 = x_1;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_22 = x_25;
goto block_24;
}
block_21:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
x_10 = lean_int_mul(x_9, x_3);
x_11 = lean_int_dec_eq(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = l_Int_Linear_Poly_leadCoeff(x_2);
lean_dec(x_2);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = l_Int_Linear_Poly_mul(x_7, x_13);
x_15 = l_Int_Linear_Poly_mul(x_8, x_9);
lean_dec(x_9);
x_16 = l_Int_Linear_Poly_combine(x_14, x_15);
x_17 = lean_nat_to_int(x_4);
x_18 = lean_int_mul(x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
x_19 = l_Int_Linear_Poly_addConst(x_16, x_18);
lean_dec(x_18);
x_20 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_6, x_19);
lean_dec(x_19);
return x_20;
}
}
block_24:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_2);
x_7 = x_22;
x_8 = x_2;
goto block_21;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_7 = x_22;
x_8 = x_23;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__dvd__right__split__dvd2__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Int_Linear_cooper__dvd__right__split__dvd2__cert(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__right__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_eq(x_9, x_11);
if (x_12 == 0)
{
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Int_Linear_instInhabitedExpr___closed__0;
x_14 = lean_int_dec_lt(x_8, x_13);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_int_dec_lt(x_13, x_10);
if (x_15 == 0)
{
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_abs(x_10);
x_17 = lean_nat_dec_eq(x_3, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__right__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_cooper__right__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__right__split__ineq__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_19; 
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_1);
x_19 = x_1;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_19 = x_22;
goto block_21;
}
block_18:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Int_Linear_Poly_leadCoeff(x_1);
lean_dec(x_1);
x_9 = lean_int_dec_eq(x_8, x_4);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l_Int_Linear_Poly_leadCoeff(x_2);
lean_dec(x_2);
x_11 = l_Int_Linear_Poly_mul(x_6, x_10);
lean_dec(x_10);
x_12 = lean_int_neg(x_4);
x_13 = l_Int_Linear_Poly_mul(x_7, x_12);
x_14 = l_Int_Linear_Poly_combine(x_11, x_13);
x_15 = lean_int_mul(x_12, x_3);
lean_dec(x_12);
x_16 = l_Int_Linear_Poly_addConst(x_14, x_15);
lean_dec(x_15);
x_17 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_5, x_16);
lean_dec(x_16);
return x_17;
}
}
block_21:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_2);
x_6 = x_19;
x_7 = x_2;
goto block_18;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_6 = x_19;
x_7 = x_20;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__right__split__ineq__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Int_Linear_cooper__right__split__ineq__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__right__split__dvd__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; 
x_9 = l_Int_Linear_Poly_leadCoeff(x_1);
x_10 = lean_int_dec_eq(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
x_5 = x_1;
goto block_8;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_5 = x_11;
goto block_8;
}
}
block_8:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Int_Linear_Poly_addConst(x_5, x_4);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__right__split__dvd__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_cooper__right__split__dvd__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnAdd(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnAdd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_Poly_casesOnAdd(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnNum(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnNum___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_Poly_casesOnNum(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_cooper__unsat__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_15, 0);
x_44 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_45 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_46 = lean_int_dec_eq(x_16, x_45);
if (x_46 == 0)
{
x_25 = x_46;
goto block_43;
}
else
{
uint8_t x_47; 
x_47 = lean_int_dec_eq(x_18, x_44);
x_25 = x_47;
goto block_43;
}
block_43:
{
if (x_25 == 0)
{
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_17, x_19);
if (x_26 == 0)
{
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_17, x_21);
if (x_27 == 0)
{
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_29 = lean_int_dec_lt(x_28, x_4);
if (x_29 == 0)
{
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_int_mul(x_5, x_20);
x_31 = lean_int_mul(x_6, x_4);
x_32 = lean_int_add(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_33 = lean_int_dec_eq(x_32, x_28);
lean_dec(x_32);
if (x_33 == 0)
{
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_int_neg(x_23);
x_35 = lean_int_neg(x_5);
x_36 = lean_int_mul(x_35, x_24);
lean_dec(x_35);
x_37 = lean_int_emod(x_36, x_4);
lean_dec(x_36);
x_38 = lean_int_sub(x_22, x_37);
x_39 = l_Int_Linear_cdiv(x_38, x_4);
lean_dec(x_38);
x_40 = lean_int_mul(x_39, x_4);
lean_dec(x_39);
x_41 = lean_int_add(x_40, x_37);
lean_dec(x_37);
lean_dec(x_40);
x_42 = lean_int_dec_lt(x_34, x_41);
lean_dec(x_41);
lean_dec(x_34);
return x_42;
}
}
}
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cooper__unsat__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Int_Linear_cooper__unsat__cert(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_emod__le__cert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_Linear_instInhabitedExpr___closed__0;
x_4 = lean_int_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_6 = lean_nat_abs(x_1);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_sub(x_5, x_7);
lean_dec(x_7);
x_9 = lean_int_dec_eq(x_2, x_8);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_emod__le__cert___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_emod__le__cert(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__le__tight__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_Int_Linear_Poly_getConst(x_2);
x_8 = l_Int_Linear_Poly_getConst(x_3);
x_9 = lean_int_neg(x_7);
x_10 = l_Int_Linear_Poly_addConst(x_2, x_9);
lean_dec(x_9);
lean_inc(x_10);
x_11 = l_Int_Linear_Poly_addConst(x_10, x_8);
x_12 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_int_sub(x_7, x_8);
lean_dec(x_8);
x_14 = lean_int_ediv(x_13, x_1);
lean_dec(x_13);
x_15 = lean_int_mul(x_1, x_14);
lean_dec(x_14);
x_16 = lean_int_sub(x_7, x_15);
lean_dec(x_15);
lean_dec(x_7);
x_17 = l_Int_Linear_Poly_addConst(x_10, x_16);
lean_dec(x_16);
x_18 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_17);
lean_dec(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__le__tight__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_dvd__le__tight__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_dvd__neg__le__tight__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int_Linear_instInhabitedExpr___closed__0;
x_6 = lean_int_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Int_Linear_Poly_getConst(x_2);
x_8 = l_Int_Linear_Poly_getConst(x_3);
x_9 = lean_int_neg(x_7);
lean_dec(x_7);
x_10 = l_Int_Linear_Poly_addConst(x_2, x_9);
x_11 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_12 = l_Int_Linear_Poly_mul(x_10, x_11);
lean_inc(x_12);
x_13 = l_Int_Linear_Poly_addConst(x_12, x_8);
x_14 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_int_sub(x_9, x_8);
lean_dec(x_8);
x_16 = lean_int_ediv(x_15, x_1);
lean_dec(x_15);
x_17 = lean_int_mul(x_1, x_16);
lean_dec(x_16);
x_18 = lean_int_sub(x_9, x_17);
lean_dec(x_17);
lean_dec(x_9);
x_19 = l_Int_Linear_Poly_addConst(x_12, x_18);
lean_dec(x_18);
x_20 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_4, x_19);
lean_dec(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_dvd__neg__le__tight__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Int_Linear_dvd__neg__le__tight__cert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_not__le__norm__expr__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Int_Linear_Expr_norm(x_4);
lean_dec(x_4);
x_6 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_7 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_8 = l_Int_Linear_Poly_mul(x_5, x_7);
x_9 = l_Int_Linear_Poly_addConst(x_8, x_6);
x_10 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_not__le__norm__expr__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_not__le__norm__expr__cert(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_neg(x_4);
lean_dec(x_4);
x_6 = l_Int_Linear_Poly_addConst(x_1, x_5);
lean_dec(x_5);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_le__of__le__cert(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_not__le__of__le__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Int_Linear_Poly_denote_x27_go___closed__0;
x_5 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_6 = l_Int_Linear_Poly_mul(x_1, x_5);
x_7 = lean_nat_to_int(x_3);
x_8 = lean_int_add(x_4, x_7);
lean_dec(x_7);
x_9 = l_Int_Linear_Poly_addConst(x_6, x_8);
lean_dec(x_8);
x_10 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_not__le__of__le__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_not__le__of__le__cert(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__def__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_5 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
x_6 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__def__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_eq__def__cert(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_eq__def_x27__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Int_Linear_norm__eq__var__cert___closed__0;
x_5 = l_Int_Linear_Expr_norm(x_2);
x_6 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_eq__def_x27__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int_Linear_eq__def_x27__cert(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_ByCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Prod(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Cooper(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_AC(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ByCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Cooper(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Gcd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_Linear_instInhabitedExpr___closed__0 = _init_l_Int_Linear_instInhabitedExpr___closed__0();
lean_mark_persistent(l_Int_Linear_instInhabitedExpr___closed__0);
l_Int_Linear_instInhabitedExpr___closed__1 = _init_l_Int_Linear_instInhabitedExpr___closed__1();
lean_mark_persistent(l_Int_Linear_instInhabitedExpr___closed__1);
l_Int_Linear_instInhabitedExpr = _init_l_Int_Linear_instInhabitedExpr();
lean_mark_persistent(l_Int_Linear_instInhabitedExpr);
l_Int_Linear_instBEqExpr___closed__0 = _init_l_Int_Linear_instBEqExpr___closed__0();
lean_mark_persistent(l_Int_Linear_instBEqExpr___closed__0);
l_Int_Linear_instBEqExpr = _init_l_Int_Linear_instBEqExpr();
lean_mark_persistent(l_Int_Linear_instBEqExpr);
l_Int_Linear_instBEqPoly___closed__0 = _init_l_Int_Linear_instBEqPoly___closed__0();
lean_mark_persistent(l_Int_Linear_instBEqPoly___closed__0);
l_Int_Linear_instBEqPoly = _init_l_Int_Linear_instBEqPoly();
lean_mark_persistent(l_Int_Linear_instBEqPoly);
l_Int_Linear_Poly_denote_x27_go___closed__0 = _init_l_Int_Linear_Poly_denote_x27_go___closed__0();
lean_mark_persistent(l_Int_Linear_Poly_denote_x27_go___closed__0);
l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___closed__0 = _init_l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_go_match__1_splitter___redArg___closed__0);
l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg___closed__0 = _init_l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_x27_match__1_splitter___redArg___closed__0);
l_Int_Linear_Expr_toPoly_x27___closed__0 = _init_l_Int_Linear_Expr_toPoly_x27___closed__0();
lean_mark_persistent(l_Int_Linear_Expr_toPoly_x27___closed__0);
l_Int_Linear_norm__eq__var__cert___closed__0 = _init_l_Int_Linear_norm__eq__var__cert___closed__0();
lean_mark_persistent(l_Int_Linear_norm__eq__var__cert___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
