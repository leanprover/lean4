// Lean compiler output
// Module: Init.Data.Int.Linear
// Imports: import all Init.Data.Int.Gcd import all Init.Data.AC import Init.LawfulBEqTactics public import Init.Data.Bool public import Init.Data.Int.Gcd public import Init.Data.RArray import Init.Data.Int.Cooper import Init.Data.Int.LemmasAux
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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Var_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_sub_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_sub_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulL_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulL_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_instInhabitedExpr_default___closed__0;
static lean_once_cell_t l_Int_Internal_Linear_instInhabitedExpr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_instInhabitedExpr_default___closed__1;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instInhabitedExpr_default;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instInhabitedExpr;
LEAN_EXPORT uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Internal_Linear_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Internal_Linear_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Internal_Linear_instBEqExpr___closed__0 = (const lean_object*)&l_Int_Internal_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Internal_Linear_instBEqExpr = (const lean_object*)&l_Int_Internal_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instBEqPoly_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Internal_Linear_instBEqPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Internal_Linear_instBEqPoly_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Internal_Linear_instBEqPoly___closed__0 = (const lean_object*)&l_Int_Internal_Linear_instBEqPoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Internal_Linear_instBEqPoly = (const lean_object*)&l_Int_Internal_Linear_instBEqPoly___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_instBEqPoly_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_instBEqPoly_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_addConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_hugeFuel;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27_go___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Expr_toPoly_x27___closed__0;
static lean_once_cell_t l_Int_Internal_Linear_Expr_toPoly_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Expr_toPoly_x27___closed__1;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_norm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getConst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_divAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_divCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divCoeffs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatEq___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatLe___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidLe___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDvd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_coeff_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_coeff_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDiseq(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDiseq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnAdd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_emod__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_emod__le__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_le__of__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_le__of__le__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_not__le__of__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_not__le__of__le__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Var_denote(lean_object* v_ctx_1_, lean_object* v_v_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_RArray_getImpl___redArg(v_ctx_1_, v_v_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Var_denote___boxed(lean_object* v_ctx_4_, lean_object* v_v_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Int_Internal_Linear_Var_denote(v_ctx_4_, v_v_5_);
lean_dec(v_v_5_);
lean_dec_ref(v_ctx_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorIdx___impl(lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_tag_nat(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorIdx___impl___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Int_Internal_Linear_Expr_ctorIdx___impl(v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 2:
{
lean_object* v_a_13_; lean_object* v_b_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_13_);
v_b_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_b_14_);
lean_dec_ref_known(v_t_11_, 2);
v___x_15_ = lean_apply_2(v_k_12_, v_a_13_, v_b_14_);
return v___x_15_;
}
case 3:
{
lean_object* v_a_16_; lean_object* v_b_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_16_);
v_b_17_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_b_17_);
lean_dec_ref_known(v_t_11_, 2);
v___x_18_ = lean_apply_2(v_k_12_, v_a_16_, v_b_17_);
return v___x_18_;
}
case 4:
{
lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_19_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_19_);
lean_dec_ref_known(v_t_11_, 1);
v___x_20_ = lean_apply_1(v_k_12_, v_a_19_);
return v___x_20_;
}
case 5:
{
lean_object* v_k_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
v_k_21_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_k_21_);
v_a_22_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_22_);
lean_dec_ref_known(v_t_11_, 2);
v___x_23_ = lean_apply_2(v_k_12_, v_k_21_, v_a_22_);
return v___x_23_;
}
case 6:
{
lean_object* v_a_24_; lean_object* v_k_25_; lean_object* v___x_26_; 
v_a_24_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_24_);
v_k_25_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_k_25_);
lean_dec_ref_known(v_t_11_, 2);
v___x_26_ = lean_apply_2(v_k_12_, v_a_24_, v_k_25_);
return v___x_26_;
}
default: 
{
lean_object* v_v_27_; lean_object* v___x_28_; 
v_v_27_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_v_27_);
lean_dec_ref(v_t_11_);
v___x_28_ = lean_apply_1(v_k_12_, v_v_27_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorElim(lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_31_, v_k_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_ctorElim___boxed(lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Int_Internal_Linear_Expr_ctorElim(v_motive_35_, v_ctorIdx_36_, v_t_37_, v_h_38_, v_k_39_);
lean_dec(v_ctorIdx_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_num_elim___redArg(lean_object* v_t_41_, lean_object* v_num_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_41_, v_num_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_num_elim(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_num_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_45_, v_num_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_var_elim___redArg(lean_object* v_t_49_, lean_object* v_var_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_49_, v_var_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_var_elim(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_var_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_53_, v_var_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_add_elim___redArg(lean_object* v_t_57_, lean_object* v_add_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_57_, v_add_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_add_elim(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_add_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_61_, v_add_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_sub_elim___redArg(lean_object* v_t_65_, lean_object* v_sub_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_65_, v_sub_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_sub_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_sub_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_69_, v_sub_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_neg_elim___redArg(lean_object* v_t_73_, lean_object* v_neg_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_73_, v_neg_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_neg_elim(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_neg_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_77_, v_neg_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulL_elim___redArg(lean_object* v_t_81_, lean_object* v_mulL_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_81_, v_mulL_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulL_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_mulL_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_85_, v_mulL_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulR_elim___redArg(lean_object* v_t_89_, lean_object* v_mulR_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_89_, v_mulR_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_mulR_elim(lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_mulR_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Int_Internal_Linear_Expr_ctorElim___redArg(v_t_93_, v_mulR_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_to_int(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__1(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Int_Internal_Linear_instInhabitedExpr_default(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__1, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__1_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__1);
return v___x_101_;
}
}
static lean_object* _init_l_Int_Internal_Linear_instInhabitedExpr(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Int_Internal_Linear_instInhabitedExpr_default;
return v___x_102_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v_b_108_; lean_object* v_b_109_; 
switch(lean_obj_tag(v_x_103_))
{
case 0:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v_v_112_; lean_object* v_v_113_; uint8_t v___x_114_; 
v_v_112_ = lean_ctor_get(v_x_103_, 0);
v_v_113_ = lean_ctor_get(v_x_104_, 0);
v___x_114_ = lean_int_dec_eq(v_v_112_, v_v_113_);
return v___x_114_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
case 1:
{
if (lean_obj_tag(v_x_104_) == 1)
{
lean_object* v_i_116_; lean_object* v_i_117_; uint8_t v___x_118_; 
v_i_116_ = lean_ctor_get(v_x_103_, 0);
v_i_117_ = lean_ctor_get(v_x_104_, 0);
v___x_118_ = lean_nat_dec_eq(v_i_116_, v_i_117_);
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
case 2:
{
if (lean_obj_tag(v_x_104_) == 2)
{
lean_object* v_a_120_; lean_object* v_b_121_; lean_object* v_a_122_; lean_object* v_b_123_; 
v_a_120_ = lean_ctor_get(v_x_103_, 0);
v_b_121_ = lean_ctor_get(v_x_103_, 1);
v_a_122_ = lean_ctor_get(v_x_104_, 0);
v_b_123_ = lean_ctor_get(v_x_104_, 1);
v_a_106_ = v_a_120_;
v_a_107_ = v_b_121_;
v_b_108_ = v_a_122_;
v_b_109_ = v_b_123_;
goto v___jp_105_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
case 3:
{
if (lean_obj_tag(v_x_104_) == 3)
{
lean_object* v_a_125_; lean_object* v_b_126_; lean_object* v_a_127_; lean_object* v_b_128_; 
v_a_125_ = lean_ctor_get(v_x_103_, 0);
v_b_126_ = lean_ctor_get(v_x_103_, 1);
v_a_127_ = lean_ctor_get(v_x_104_, 0);
v_b_128_ = lean_ctor_get(v_x_104_, 1);
v_a_106_ = v_a_125_;
v_a_107_ = v_b_126_;
v_b_108_ = v_a_127_;
v_b_109_ = v_b_128_;
goto v___jp_105_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
case 4:
{
if (lean_obj_tag(v_x_104_) == 4)
{
lean_object* v_a_130_; lean_object* v_a_131_; 
v_a_130_ = lean_ctor_get(v_x_103_, 0);
v_a_131_ = lean_ctor_get(v_x_104_, 0);
v_x_103_ = v_a_130_;
v_x_104_ = v_a_131_;
goto _start;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
case 5:
{
if (lean_obj_tag(v_x_104_) == 5)
{
lean_object* v_k_134_; lean_object* v_a_135_; lean_object* v_k_136_; lean_object* v_a_137_; uint8_t v___x_138_; 
v_k_134_ = lean_ctor_get(v_x_103_, 0);
v_a_135_ = lean_ctor_get(v_x_103_, 1);
v_k_136_ = lean_ctor_get(v_x_104_, 0);
v_a_137_ = lean_ctor_get(v_x_104_, 1);
v___x_138_ = lean_int_dec_eq(v_k_134_, v_k_136_);
if (v___x_138_ == 0)
{
return v___x_138_;
}
else
{
v_x_103_ = v_a_135_;
v_x_104_ = v_a_137_;
goto _start;
}
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
default: 
{
if (lean_obj_tag(v_x_104_) == 6)
{
lean_object* v_a_141_; lean_object* v_k_142_; lean_object* v_a_143_; lean_object* v_k_144_; uint8_t v___x_145_; 
v_a_141_ = lean_ctor_get(v_x_103_, 0);
v_k_142_ = lean_ctor_get(v_x_103_, 1);
v_a_143_ = lean_ctor_get(v_x_104_, 0);
v_k_144_ = lean_ctor_get(v_x_104_, 1);
v___x_145_ = l_Int_Internal_Linear_instBEqExpr_beq(v_a_141_, v_a_143_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_int_dec_eq(v_k_142_, v_k_144_);
return v___x_146_;
}
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
v___jp_105_:
{
uint8_t v___x_110_; 
v___x_110_ = l_Int_Internal_Linear_instBEqExpr_beq(v_a_106_, v_b_108_);
if (v___x_110_ == 0)
{
return v___x_110_;
}
else
{
v_x_103_ = v_a_107_;
v_x_104_ = v_b_109_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instBEqExpr_beq___boxed(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Int_Internal_Linear_instBEqExpr_beq(v_x_148_, v_x_149_);
lean_dec_ref(v_x_149_);
lean_dec_ref(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denote(lean_object* v_ctx_154_, lean_object* v_x_155_){
_start:
{
switch(lean_obj_tag(v_x_155_))
{
case 0:
{
lean_object* v_v_156_; 
v_v_156_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_v_156_);
return v_v_156_;
}
case 1:
{
lean_object* v_i_157_; lean_object* v___x_158_; 
v_i_157_ = lean_ctor_get(v_x_155_, 0);
v___x_158_ = l_Lean_RArray_getImpl___redArg(v_ctx_154_, v_i_157_);
return v___x_158_;
}
case 2:
{
lean_object* v_a_159_; lean_object* v_b_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_159_ = lean_ctor_get(v_x_155_, 0);
v_b_160_ = lean_ctor_get(v_x_155_, 1);
v___x_161_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_a_159_);
v___x_162_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_b_160_);
v___x_163_ = lean_int_add(v___x_161_, v___x_162_);
lean_dec(v___x_162_);
lean_dec(v___x_161_);
return v___x_163_;
}
case 3:
{
lean_object* v_a_164_; lean_object* v_b_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_164_ = lean_ctor_get(v_x_155_, 0);
v_b_165_ = lean_ctor_get(v_x_155_, 1);
v___x_166_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_a_164_);
v___x_167_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_b_165_);
v___x_168_ = lean_int_sub(v___x_166_, v___x_167_);
lean_dec(v___x_167_);
lean_dec(v___x_166_);
return v___x_168_;
}
case 4:
{
lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_a_169_ = lean_ctor_get(v_x_155_, 0);
v___x_170_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_a_169_);
v___x_171_ = lean_int_neg(v___x_170_);
lean_dec(v___x_170_);
return v___x_171_;
}
case 5:
{
lean_object* v_k_172_; lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_k_172_ = lean_ctor_get(v_x_155_, 0);
v_a_173_ = lean_ctor_get(v_x_155_, 1);
v___x_174_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_a_173_);
v___x_175_ = lean_int_mul(v_k_172_, v___x_174_);
lean_dec(v___x_174_);
return v___x_175_;
}
default: 
{
lean_object* v_a_176_; lean_object* v_k_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_176_ = lean_ctor_get(v_x_155_, 0);
v_k_177_ = lean_ctor_get(v_x_155_, 1);
v___x_178_ = l_Int_Internal_Linear_Expr_denote(v_ctx_154_, v_a_176_);
v___x_179_ = lean_int_mul(v___x_178_, v_k_177_);
lean_dec(v___x_178_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denote___boxed(lean_object* v_ctx_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Int_Internal_Linear_Expr_denote(v_ctx_180_, v_x_181_);
lean_dec_ref(v_x_181_);
lean_dec_ref(v_ctx_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorIdx___impl(lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_tag_nat(v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorIdx___impl___boxed(lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Int_Internal_Linear_Poly_ctorIdx___impl(v_x_185_);
lean_dec_ref(v_x_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim___redArg(lean_object* v_t_187_, lean_object* v_k_188_){
_start:
{
if (lean_obj_tag(v_t_187_) == 0)
{
lean_object* v_k_189_; lean_object* v___x_190_; 
v_k_189_ = lean_ctor_get(v_t_187_, 0);
lean_inc(v_k_189_);
lean_dec_ref_known(v_t_187_, 1);
v___x_190_ = lean_apply_1(v_k_188_, v_k_189_);
return v___x_190_;
}
else
{
lean_object* v_k_191_; lean_object* v_v_192_; lean_object* v_p_193_; lean_object* v___x_194_; 
v_k_191_ = lean_ctor_get(v_t_187_, 0);
lean_inc(v_k_191_);
v_v_192_ = lean_ctor_get(v_t_187_, 1);
lean_inc(v_v_192_);
v_p_193_ = lean_ctor_get(v_t_187_, 2);
lean_inc_ref(v_p_193_);
lean_dec_ref_known(v_t_187_, 3);
v___x_194_ = lean_apply_3(v_k_188_, v_k_191_, v_v_192_, v_p_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim(lean_object* v_motive_195_, lean_object* v_ctorIdx_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_k_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_197_, v_k_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim___boxed(lean_object* v_motive_201_, lean_object* v_ctorIdx_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_k_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Int_Internal_Linear_Poly_ctorElim(v_motive_201_, v_ctorIdx_202_, v_t_203_, v_h_204_, v_k_205_);
lean_dec(v_ctorIdx_202_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_num_elim___redArg(lean_object* v_t_207_, lean_object* v_num_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_207_, v_num_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_num_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_num_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_211_, v_num_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_add_elim___redArg(lean_object* v_t_215_, lean_object* v_add_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_215_, v_add_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_add_elim(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_add_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_219_, v_add_221_);
return v___x_222_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v_k_225_; lean_object* v_k_226_; uint8_t v___x_227_; 
v_k_225_ = lean_ctor_get(v_x_223_, 0);
v_k_226_ = lean_ctor_get(v_x_224_, 0);
v___x_227_ = lean_int_dec_eq(v_k_225_, v_k_226_);
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
else
{
if (lean_obj_tag(v_x_224_) == 1)
{
lean_object* v_k_229_; lean_object* v_v_230_; lean_object* v_p_231_; lean_object* v_k_232_; lean_object* v_v_233_; lean_object* v_p_234_; uint8_t v___x_235_; 
v_k_229_ = lean_ctor_get(v_x_223_, 0);
v_v_230_ = lean_ctor_get(v_x_223_, 1);
v_p_231_ = lean_ctor_get(v_x_223_, 2);
v_k_232_ = lean_ctor_get(v_x_224_, 0);
v_v_233_ = lean_ctor_get(v_x_224_, 1);
v_p_234_ = lean_ctor_get(v_x_224_, 2);
v___x_235_ = lean_int_dec_eq(v_k_229_, v_k_232_);
if (v___x_235_ == 0)
{
return v___x_235_;
}
else
{
uint8_t v___x_236_; 
v___x_236_ = lean_nat_dec_eq(v_v_230_, v_v_233_);
if (v___x_236_ == 0)
{
return v___x_236_;
}
else
{
v_x_223_ = v_p_231_;
v_x_224_ = v_p_234_;
goto _start;
}
}
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instBEqPoly_beq___boxed(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_239_, v_x_240_);
lean_dec_ref(v_x_240_);
lean_dec_ref(v_x_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_, lean_object* v_h__3_249_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_dec(v_h__2_248_);
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v_k_250_; lean_object* v_k_251_; lean_object* v___x_252_; 
lean_dec(v_h__3_249_);
v_k_250_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_k_250_);
lean_dec_ref_known(v_x_245_, 1);
v_k_251_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_k_251_);
lean_dec_ref_known(v_x_246_, 1);
v___x_252_ = lean_apply_2(v_h__1_247_, v_k_250_, v_k_251_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
lean_dec(v_h__1_247_);
v___x_253_ = lean_apply_4(v_h__3_249_, v_x_245_, v_x_246_, lean_box(0), lean_box(0));
return v___x_253_;
}
}
else
{
lean_dec(v_h__1_247_);
if (lean_obj_tag(v_x_246_) == 1)
{
lean_object* v_k_254_; lean_object* v_v_255_; lean_object* v_p_256_; lean_object* v_k_257_; lean_object* v_v_258_; lean_object* v_p_259_; lean_object* v___x_260_; 
lean_dec(v_h__3_249_);
v_k_254_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_k_254_);
v_v_255_ = lean_ctor_get(v_x_245_, 1);
lean_inc(v_v_255_);
v_p_256_ = lean_ctor_get(v_x_245_, 2);
lean_inc_ref(v_p_256_);
lean_dec_ref_known(v_x_245_, 3);
v_k_257_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_k_257_);
v_v_258_ = lean_ctor_get(v_x_246_, 1);
lean_inc(v_v_258_);
v_p_259_ = lean_ctor_get(v_x_246_, 2);
lean_inc_ref(v_p_259_);
lean_dec_ref_known(v_x_246_, 3);
v___x_260_ = lean_apply_6(v_h__2_248_, v_k_254_, v_v_255_, v_p_256_, v_k_257_, v_v_258_, v_p_259_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; 
lean_dec(v_h__2_248_);
v___x_261_ = lean_apply_4(v_h__3_249_, v_x_245_, v_x_246_, lean_box(0), lean_box(0));
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_, lean_object* v_h__3_267_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_dec(v_h__2_266_);
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v_k_268_; lean_object* v_k_269_; lean_object* v___x_270_; 
lean_dec(v_h__3_267_);
v_k_268_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_k_268_);
lean_dec_ref_known(v_x_263_, 1);
v_k_269_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_k_269_);
lean_dec_ref_known(v_x_264_, 1);
v___x_270_ = lean_apply_2(v_h__1_265_, v_k_268_, v_k_269_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
lean_dec(v_h__1_265_);
v___x_271_ = lean_apply_4(v_h__3_267_, v_x_263_, v_x_264_, lean_box(0), lean_box(0));
return v___x_271_;
}
}
else
{
lean_dec(v_h__1_265_);
if (lean_obj_tag(v_x_264_) == 1)
{
lean_object* v_k_272_; lean_object* v_v_273_; lean_object* v_p_274_; lean_object* v_k_275_; lean_object* v_v_276_; lean_object* v_p_277_; lean_object* v___x_278_; 
lean_dec(v_h__3_267_);
v_k_272_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_k_272_);
v_v_273_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_v_273_);
v_p_274_ = lean_ctor_get(v_x_263_, 2);
lean_inc_ref(v_p_274_);
lean_dec_ref_known(v_x_263_, 3);
v_k_275_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_k_275_);
v_v_276_ = lean_ctor_get(v_x_264_, 1);
lean_inc(v_v_276_);
v_p_277_ = lean_ctor_get(v_x_264_, 2);
lean_inc_ref(v_p_277_);
lean_dec_ref_known(v_x_264_, 3);
v___x_278_ = lean_apply_6(v_h__2_266_, v_k_272_, v_v_273_, v_p_274_, v_k_275_, v_v_276_, v_p_277_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
lean_dec(v_h__2_266_);
v___x_279_ = lean_apply_4(v_h__3_267_, v_x_263_, v_x_264_, lean_box(0), lean_box(0));
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denote(lean_object* v_ctx_280_, lean_object* v_p_281_){
_start:
{
if (lean_obj_tag(v_p_281_) == 0)
{
lean_object* v_k_282_; 
v_k_282_ = lean_ctor_get(v_p_281_, 0);
lean_inc(v_k_282_);
return v_k_282_;
}
else
{
lean_object* v_k_283_; lean_object* v_v_284_; lean_object* v_p_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_k_283_ = lean_ctor_get(v_p_281_, 0);
v_v_284_ = lean_ctor_get(v_p_281_, 1);
v_p_285_ = lean_ctor_get(v_p_281_, 2);
v___x_286_ = l_Lean_RArray_getImpl___redArg(v_ctx_280_, v_v_284_);
v___x_287_ = lean_int_mul(v_k_283_, v___x_286_);
lean_dec(v___x_286_);
v___x_288_ = l_Int_Internal_Linear_Poly_denote(v_ctx_280_, v_p_285_);
v___x_289_ = lean_int_add(v___x_287_, v___x_288_);
lean_dec(v___x_288_);
lean_dec(v___x_287_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denote___boxed(lean_object* v_ctx_290_, lean_object* v_p_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Int_Internal_Linear_Poly_denote(v_ctx_290_, v_p_291_);
lean_dec_ref(v_p_291_);
lean_dec_ref(v_ctx_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_denote_match__1_splitter___redArg(lean_object* v_p_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
_start:
{
if (lean_obj_tag(v_p_293_) == 0)
{
lean_object* v_k_296_; lean_object* v___x_297_; 
lean_dec(v_h__2_295_);
v_k_296_ = lean_ctor_get(v_p_293_, 0);
lean_inc(v_k_296_);
lean_dec_ref_known(v_p_293_, 1);
v___x_297_ = lean_apply_1(v_h__1_294_, v_k_296_);
return v___x_297_;
}
else
{
lean_object* v_k_298_; lean_object* v_v_299_; lean_object* v_p_300_; lean_object* v___x_301_; 
lean_dec(v_h__1_294_);
v_k_298_ = lean_ctor_get(v_p_293_, 0);
lean_inc(v_k_298_);
v_v_299_ = lean_ctor_get(v_p_293_, 1);
lean_inc(v_v_299_);
v_p_300_ = lean_ctor_get(v_p_293_, 2);
lean_inc_ref(v_p_300_);
lean_dec_ref_known(v_p_293_, 3);
v___x_301_ = lean_apply_3(v_h__2_295_, v_k_298_, v_v_299_, v_p_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_denote_match__1_splitter(lean_object* v_motive_302_, lean_object* v_p_303_, lean_object* v_h__1_304_, lean_object* v_h__2_305_){
_start:
{
if (lean_obj_tag(v_p_303_) == 0)
{
lean_object* v_k_306_; lean_object* v___x_307_; 
lean_dec(v_h__2_305_);
v_k_306_ = lean_ctor_get(v_p_303_, 0);
lean_inc(v_k_306_);
lean_dec_ref_known(v_p_303_, 1);
v___x_307_ = lean_apply_1(v_h__1_304_, v_k_306_);
return v___x_307_;
}
else
{
lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v_p_310_; lean_object* v___x_311_; 
lean_dec(v_h__1_304_);
v_k_308_ = lean_ctor_get(v_p_303_, 0);
lean_inc(v_k_308_);
v_v_309_ = lean_ctor_get(v_p_303_, 1);
lean_inc(v_v_309_);
v_p_310_ = lean_ctor_get(v_p_303_, 2);
lean_inc_ref(v_p_310_);
lean_dec_ref_known(v_p_303_, 3);
v___x_311_ = lean_apply_3(v_h__2_305_, v_k_308_, v_v_309_, v_p_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object* v_p_312_, lean_object* v_k_313_){
_start:
{
if (lean_obj_tag(v_p_312_) == 0)
{
lean_object* v_k_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_k_314_ = lean_ctor_get(v_p_312_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_p_312_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v_p_312_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_k_314_);
lean_dec(v_p_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_int_add(v_k_313_, v_k_314_);
lean_dec(v_k_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_p_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_k_323_ = lean_ctor_get(v_p_312_, 0);
v_v_324_ = lean_ctor_get(v_p_312_, 1);
v_p_325_ = lean_ctor_get(v_p_312_, 2);
v_isSharedCheck_333_ = !lean_is_exclusive(v_p_312_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v_p_312_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_p_325_);
lean_inc(v_v_324_);
lean_inc(v_k_323_);
lean_dec(v_p_312_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = l_Int_Internal_Linear_Poly_addConst(v_p_325_, v_k_313_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 2, v___x_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_k_323_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_v_324_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_addConst___boxed(lean_object* v_p_334_, lean_object* v_k_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Int_Internal_Linear_Poly_addConst(v_p_334_, v_k_335_);
lean_dec(v_k_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_insert(lean_object* v_k_337_, lean_object* v_v_338_, lean_object* v_p_339_){
_start:
{
if (lean_obj_tag(v_p_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_340_, 0, v_k_337_);
lean_ctor_set(v___x_340_, 1, v_v_338_);
lean_ctor_set(v___x_340_, 2, v_p_339_);
return v___x_340_;
}
else
{
lean_object* v_k_341_; lean_object* v_v_342_; lean_object* v_p_343_; uint8_t v___x_344_; 
v_k_341_ = lean_ctor_get(v_p_339_, 0);
v_v_342_ = lean_ctor_get(v_p_339_, 1);
v_p_343_ = lean_ctor_get(v_p_339_, 2);
v___x_344_ = l_Nat_blt(v_v_342_, v_v_338_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_359_; 
lean_inc_ref(v_p_343_);
lean_inc(v_v_342_);
lean_inc(v_k_341_);
v_isSharedCheck_359_ = !lean_is_exclusive(v_p_339_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_360_ = lean_ctor_get(v_p_339_, 2);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_p_339_, 1);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_p_339_, 0);
lean_dec(v_unused_362_);
v___x_346_ = v_p_339_;
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_p_339_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___x_348_; 
v___x_348_ = lean_nat_dec_eq(v_v_338_, v_v_342_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_Int_Internal_Linear_Poly_insert(v_k_337_, v_v_338_, v_p_343_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 2, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_k_341_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_v_342_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
lean_dec(v_v_338_);
v___x_353_ = lean_int_add(v_k_337_, v_k_341_);
lean_dec(v_k_341_);
lean_dec(v_k_337_);
v___x_354_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_355_ = lean_int_dec_eq(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_357_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_353_);
v___x_357_ = v___x_346_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_v_342_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_p_343_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
lean_dec(v___x_353_);
lean_del_object(v___x_346_);
lean_dec(v_v_342_);
return v_p_343_;
}
}
}
}
else
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_363_, 0, v_k_337_);
lean_ctor_set(v___x_363_, 1, v_v_338_);
lean_ctor_set(v___x_363_, 2, v_p_339_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_norm(lean_object* v_p_364_){
_start:
{
if (lean_obj_tag(v_p_364_) == 0)
{
return v_p_364_;
}
else
{
lean_object* v_k_365_; lean_object* v_v_366_; lean_object* v_p_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_k_365_ = lean_ctor_get(v_p_364_, 0);
lean_inc(v_k_365_);
v_v_366_ = lean_ctor_get(v_p_364_, 1);
lean_inc(v_v_366_);
v_p_367_ = lean_ctor_get(v_p_364_, 2);
lean_inc_ref(v_p_367_);
lean_dec_ref_known(v_p_364_, 3);
v___x_368_ = l_Int_Internal_Linear_Poly_norm(v_p_367_);
v___x_369_ = l_Int_Internal_Linear_Poly_insert(v_k_365_, v_v_366_, v___x_368_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_append(lean_object* v_p_u2081_370_, lean_object* v_p_u2082_371_){
_start:
{
if (lean_obj_tag(v_p_u2081_370_) == 0)
{
lean_object* v_k_372_; lean_object* v___x_373_; 
v_k_372_ = lean_ctor_get(v_p_u2081_370_, 0);
lean_inc(v_k_372_);
lean_dec_ref_known(v_p_u2081_370_, 1);
v___x_373_ = l_Int_Internal_Linear_Poly_addConst(v_p_u2082_371_, v_k_372_);
lean_dec(v_k_372_);
return v___x_373_;
}
else
{
lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_p_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_k_374_ = lean_ctor_get(v_p_u2081_370_, 0);
v_v_375_ = lean_ctor_get(v_p_u2081_370_, 1);
v_p_376_ = lean_ctor_get(v_p_u2081_370_, 2);
v_isSharedCheck_384_ = !lean_is_exclusive(v_p_u2081_370_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v_p_u2081_370_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_p_376_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
lean_dec(v_p_u2081_370_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = l_Int_Internal_Linear_Poly_append(v_p_376_, v_p_u2082_371_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 2, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_combine_x27(lean_object* v_fuel_385_, lean_object* v_p_u2081_386_, lean_object* v_p_u2082_387_){
_start:
{
lean_object* v_zero_388_; uint8_t v_isZero_389_; 
v_zero_388_ = lean_unsigned_to_nat(0u);
v_isZero_389_ = lean_nat_dec_eq(v_fuel_385_, v_zero_388_);
if (v_isZero_389_ == 1)
{
lean_object* v___x_390_; 
lean_dec(v_fuel_385_);
v___x_390_ = l_Int_Internal_Linear_Poly_append(v_p_u2081_386_, v_p_u2082_387_);
return v___x_390_;
}
else
{
lean_object* v_one_391_; lean_object* v_n_392_; 
v_one_391_ = lean_unsigned_to_nat(1u);
v_n_392_ = lean_nat_sub(v_fuel_385_, v_one_391_);
lean_dec(v_fuel_385_);
if (lean_obj_tag(v_p_u2081_386_) == 0)
{
if (lean_obj_tag(v_p_u2082_387_) == 0)
{
lean_object* v_k_393_; lean_object* v_k_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_n_392_);
v_k_393_ = lean_ctor_get(v_p_u2081_386_, 0);
lean_inc(v_k_393_);
lean_dec_ref_known(v_p_u2081_386_, 1);
v_k_394_ = lean_ctor_get(v_p_u2082_387_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_p_u2082_387_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_p_u2082_387_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_k_394_);
lean_dec(v_p_u2082_387_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_int_add(v_k_393_, v_k_394_);
lean_dec(v_k_394_);
lean_dec(v_k_393_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_k_403_; lean_object* v_v_404_; lean_object* v_p_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_k_403_ = lean_ctor_get(v_p_u2082_387_, 0);
v_v_404_ = lean_ctor_get(v_p_u2082_387_, 1);
v_p_405_ = lean_ctor_get(v_p_u2082_387_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_p_u2082_387_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v_p_u2082_387_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_p_405_);
lean_inc(v_v_404_);
lean_inc(v_k_403_);
lean_dec(v_p_u2082_387_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_392_, v_p_u2081_386_, v_p_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 2, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_k_403_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_v_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
if (lean_obj_tag(v_p_u2082_387_) == 0)
{
lean_object* v_k_414_; lean_object* v_v_415_; lean_object* v_p_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_k_414_ = lean_ctor_get(v_p_u2081_386_, 0);
v_v_415_ = lean_ctor_get(v_p_u2081_386_, 1);
v_p_416_ = lean_ctor_get(v_p_u2081_386_, 2);
v_isSharedCheck_424_ = !lean_is_exclusive(v_p_u2081_386_);
if (v_isSharedCheck_424_ == 0)
{
v___x_418_ = v_p_u2081_386_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_p_416_);
lean_inc(v_v_415_);
lean_inc(v_k_414_);
lean_dec(v_p_u2081_386_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_392_, v_p_416_, v_p_u2082_387_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 2, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_k_414_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_v_415_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_object* v_k_425_; lean_object* v_v_426_; lean_object* v_p_427_; lean_object* v_k_428_; lean_object* v_v_429_; lean_object* v_p_430_; uint8_t v___x_431_; 
v_k_425_ = lean_ctor_get(v_p_u2081_386_, 0);
v_v_426_ = lean_ctor_get(v_p_u2081_386_, 1);
v_p_427_ = lean_ctor_get(v_p_u2081_386_, 2);
v_k_428_ = lean_ctor_get(v_p_u2082_387_, 0);
v_v_429_ = lean_ctor_get(v_p_u2082_387_, 1);
v_p_430_ = lean_ctor_get(v_p_u2082_387_, 2);
v___x_431_ = lean_nat_dec_eq(v_v_426_, v_v_429_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = l_Nat_blt(v_v_429_, v_v_426_);
if (v___x_432_ == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
lean_inc_ref(v_p_430_);
lean_inc(v_v_429_);
lean_inc(v_k_428_);
v_isSharedCheck_440_ = !lean_is_exclusive(v_p_u2082_387_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_441_ = lean_ctor_get(v_p_u2082_387_, 2);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_p_u2082_387_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_p_u2082_387_, 0);
lean_dec(v_unused_443_);
v___x_434_ = v_p_u2082_387_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_p_u2082_387_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_392_, v_p_u2081_386_, v_p_430_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 2, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_k_428_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_v_429_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_451_; 
lean_inc_ref(v_p_427_);
lean_inc(v_v_426_);
lean_inc(v_k_425_);
v_isSharedCheck_451_ = !lean_is_exclusive(v_p_u2081_386_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_452_ = lean_ctor_get(v_p_u2081_386_, 2);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_p_u2081_386_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_p_u2081_386_, 0);
lean_dec(v_unused_454_);
v___x_445_ = v_p_u2081_386_;
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_p_u2081_386_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_392_, v_p_427_, v_p_u2082_387_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 2, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_k_425_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_v_426_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_466_; 
lean_inc_ref(v_p_430_);
lean_inc(v_k_428_);
lean_inc_ref(v_p_427_);
lean_inc(v_v_426_);
lean_inc(v_k_425_);
lean_dec_ref_known(v_p_u2081_386_, 3);
v_isSharedCheck_466_ = !lean_is_exclusive(v_p_u2082_387_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; lean_object* v_unused_469_; 
v_unused_467_ = lean_ctor_get(v_p_u2082_387_, 2);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_p_u2082_387_, 1);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_p_u2082_387_, 0);
lean_dec(v_unused_469_);
v___x_456_ = v_p_u2082_387_;
v_isShared_457_ = v_isSharedCheck_466_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_p_u2082_387_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_466_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_a_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_a_458_ = lean_int_add(v_k_425_, v_k_428_);
lean_dec(v_k_428_);
lean_dec(v_k_425_);
v___x_459_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_460_ = lean_int_dec_eq(v_a_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_392_, v_p_427_, v_p_430_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 2, v___x_461_);
lean_ctor_set(v___x_456_, 1, v_v_426_);
lean_ctor_set(v___x_456_, 0, v_a_458_);
v___x_463_ = v___x_456_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_v_426_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_dec(v_a_458_);
lean_del_object(v___x_456_);
lean_dec(v_v_426_);
v_fuel_385_ = v_n_392_;
v_p_u2081_386_ = v_p_427_;
v_p_u2082_387_ = v_p_430_;
goto _start;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Int_Internal_Linear_hugeFuel(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_unsigned_to_nat(100000000u);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_combine(lean_object* v_p_u2081_471_, lean_object* v_p_u2082_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(100000000u);
v___x_474_ = l_Int_Internal_Linear_Poly_combine_x27(v___x_473_, v_p_u2081_471_, v_p_u2082_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27_go(lean_object* v_coeff_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
switch(lean_obj_tag(v_a_476_))
{
case 0:
{
lean_object* v_v_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_v_478_ = lean_ctor_get(v_a_476_, 0);
v___x_479_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_480_ = lean_int_dec_eq(v_v_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_int_mul(v_coeff_475_, v_v_478_);
lean_dec(v_coeff_475_);
v___x_482_ = l_Int_Internal_Linear_Poly_addConst(v_a_477_, v___x_481_);
lean_dec(v___x_481_);
return v___x_482_;
}
else
{
lean_dec(v_coeff_475_);
return v_a_477_;
}
}
case 1:
{
lean_object* v_i_483_; lean_object* v___x_484_; 
v_i_483_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_i_483_);
v___x_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_484_, 0, v_coeff_475_);
lean_ctor_set(v___x_484_, 1, v_i_483_);
lean_ctor_set(v___x_484_, 2, v_a_477_);
return v___x_484_;
}
case 2:
{
lean_object* v_a_485_; lean_object* v_b_486_; lean_object* v___x_487_; 
v_a_485_ = lean_ctor_get(v_a_476_, 0);
v_b_486_ = lean_ctor_get(v_a_476_, 1);
lean_inc(v_coeff_475_);
v___x_487_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v_coeff_475_, v_b_486_, v_a_477_);
v_a_476_ = v_a_485_;
v_a_477_ = v___x_487_;
goto _start;
}
case 3:
{
lean_object* v_a_489_; lean_object* v_b_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_a_489_ = lean_ctor_get(v_a_476_, 0);
v_b_490_ = lean_ctor_get(v_a_476_, 1);
v___x_491_ = lean_int_neg(v_coeff_475_);
v___x_492_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v___x_491_, v_b_490_, v_a_477_);
v_a_476_ = v_a_489_;
v_a_477_ = v___x_492_;
goto _start;
}
case 4:
{
lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_494_ = lean_ctor_get(v_a_476_, 0);
v___x_495_ = lean_int_neg(v_coeff_475_);
lean_dec(v_coeff_475_);
v_coeff_475_ = v___x_495_;
v_a_476_ = v_a_494_;
goto _start;
}
case 5:
{
lean_object* v_k_497_; lean_object* v_a_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_k_497_ = lean_ctor_get(v_a_476_, 0);
v_a_498_ = lean_ctor_get(v_a_476_, 1);
v___x_499_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_500_ = lean_int_dec_eq(v_k_497_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_int_mul(v_coeff_475_, v_k_497_);
lean_dec(v_coeff_475_);
v_coeff_475_ = v___x_501_;
v_a_476_ = v_a_498_;
goto _start;
}
else
{
lean_dec(v_coeff_475_);
return v_a_477_;
}
}
default: 
{
lean_object* v_a_503_; lean_object* v_k_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_a_503_ = lean_ctor_get(v_a_476_, 0);
v_k_504_ = lean_ctor_get(v_a_476_, 1);
v___x_505_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_506_ = lean_int_dec_eq(v_k_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_int_mul(v_coeff_475_, v_k_504_);
lean_dec(v_coeff_475_);
v_coeff_475_ = v___x_507_;
v_a_476_ = v_a_503_;
goto _start;
}
else
{
lean_dec(v_coeff_475_);
return v_a_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27_go___boxed(lean_object* v_coeff_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v_coeff_509_, v_a_510_, v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_512_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_to_int(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27(lean_object* v_e_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_519_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__1, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1);
v___x_520_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v___x_518_, v_e_517_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27___boxed(lean_object* v_e_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Int_Internal_Linear_Expr_toPoly_x27(v_e_521_);
lean_dec_ref(v_e_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_norm(lean_object* v_e_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Int_Internal_Linear_Expr_toPoly_x27(v_e_523_);
v___x_525_ = l_Int_Internal_Linear_Poly_norm(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_norm___boxed(lean_object* v_e_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Int_Internal_Linear_Expr_norm(v_e_526_);
lean_dec_ref(v_e_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cdiv(lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_int_neg(v_a_528_);
v___x_531_ = lean_int_ediv(v___x_530_, v_b_529_);
lean_dec(v___x_530_);
v___x_532_ = lean_int_neg(v___x_531_);
lean_dec(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cdiv___boxed(lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Int_Internal_Linear_cdiv(v_a_533_, v_b_534_);
lean_dec(v_b_534_);
lean_dec(v_a_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cmod(lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_int_neg(v_a_536_);
v___x_539_ = lean_int_emod(v___x_538_, v_b_537_);
lean_dec(v___x_538_);
v___x_540_ = lean_int_neg(v___x_539_);
lean_dec(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cmod___boxed(lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Int_Internal_Linear_cmod(v_a_541_, v_b_542_);
lean_dec(v_b_542_);
lean_dec(v_a_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object* v_x_544_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_k_545_; 
v_k_545_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_k_545_);
return v_k_545_;
}
else
{
lean_object* v_p_546_; 
v_p_546_ = lean_ctor_get(v_x_544_, 2);
v_x_544_ = v_p_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getConst___boxed(lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Int_Internal_Linear_Poly_getConst(v_x_548_);
lean_dec_ref(v_x_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_div(lean_object* v_k_550_, lean_object* v_x_551_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_k_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_k_552_ = lean_ctor_get(v_x_551_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v_x_551_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_k_552_);
lean_dec(v_x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Int_Internal_Linear_cdiv(v_k_552_, v_k_550_);
lean_dec(v_k_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_object* v_k_561_; lean_object* v_v_562_; lean_object* v_p_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v_k_561_ = lean_ctor_get(v_x_551_, 0);
v_v_562_ = lean_ctor_get(v_x_551_, 1);
v_p_563_ = lean_ctor_get(v_x_551_, 2);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_572_ == 0)
{
v___x_565_ = v_x_551_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_p_563_);
lean_inc(v_v_562_);
lean_inc(v_k_561_);
lean_dec(v_x_551_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = lean_int_ediv(v_k_561_, v_k_550_);
lean_dec(v_k_561_);
v___x_568_ = l_Int_Internal_Linear_Poly_div(v_k_550_, v_p_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 2, v___x_568_);
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_v_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v___x_568_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_div___boxed(lean_object* v_k_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Int_Internal_Linear_Poly_div(v_k_573_, v_x_574_);
lean_dec(v_k_573_);
return v_res_575_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_divAll(lean_object* v_k_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v_k_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_k_578_ = lean_ctor_get(v_x_577_, 0);
v___x_579_ = lean_int_emod(v_k_578_, v_k_576_);
v___x_580_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_581_ = lean_int_dec_eq(v___x_579_, v___x_580_);
lean_dec(v___x_579_);
return v___x_581_;
}
else
{
lean_object* v_k_582_; lean_object* v_p_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_k_582_ = lean_ctor_get(v_x_577_, 0);
v_p_583_ = lean_ctor_get(v_x_577_, 2);
v___x_584_ = lean_int_emod(v_k_582_, v_k_576_);
v___x_585_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_586_ = lean_int_dec_eq(v___x_584_, v___x_585_);
lean_dec(v___x_584_);
if (v___x_586_ == 0)
{
return v___x_586_;
}
else
{
v_x_577_ = v_p_583_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divAll___boxed(lean_object* v_k_588_, lean_object* v_x_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_Int_Internal_Linear_Poly_divAll(v_k_588_, v_x_589_);
lean_dec_ref(v_x_589_);
lean_dec(v_k_588_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_divCoeffs(lean_object* v_k_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
uint8_t v___x_594_; 
v___x_594_ = 1;
return v___x_594_;
}
else
{
lean_object* v_k_595_; lean_object* v_p_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_k_595_ = lean_ctor_get(v_x_593_, 0);
v_p_596_ = lean_ctor_get(v_x_593_, 2);
v___x_597_ = lean_int_emod(v_k_595_, v_k_592_);
v___x_598_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_599_ = lean_int_dec_eq(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
if (v___x_599_ == 0)
{
return v___x_599_;
}
else
{
v_x_593_ = v_p_596_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divCoeffs___boxed(lean_object* v_k_601_, lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Int_Internal_Linear_Poly_divCoeffs(v_k_601_, v_x_602_);
lean_dec_ref(v_x_602_);
lean_dec(v_k_601_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27(lean_object* v_p_605_, lean_object* v_k_606_){
_start:
{
if (lean_obj_tag(v_p_605_) == 0)
{
lean_object* v_k_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_k_607_ = lean_ctor_get(v_p_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_p_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v_p_605_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_k_607_);
lean_dec(v_p_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_int_mul(v_k_606_, v_k_607_);
lean_dec(v_k_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_k_616_; lean_object* v_v_617_; lean_object* v_p_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_627_; 
v_k_616_ = lean_ctor_get(v_p_605_, 0);
v_v_617_ = lean_ctor_get(v_p_605_, 1);
v_p_618_ = lean_ctor_get(v_p_605_, 2);
v_isSharedCheck_627_ = !lean_is_exclusive(v_p_605_);
if (v_isSharedCheck_627_ == 0)
{
v___x_620_ = v_p_605_;
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_p_618_);
lean_inc(v_v_617_);
lean_inc(v_k_616_);
lean_dec(v_p_605_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_622_ = lean_int_mul(v_k_606_, v_k_616_);
lean_dec(v_k_616_);
v___x_623_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_618_, v_k_606_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 2, v___x_623_);
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_v_617_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27___boxed(lean_object* v_p_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_628_, v_k_629_);
lean_dec(v_k_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul(lean_object* v_p_631_, lean_object* v_k_632_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_634_ = lean_int_dec_eq(v_k_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_631_, v_k_632_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; 
lean_dec_ref(v_p_631_);
v___x_636_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__1, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul___boxed(lean_object* v_p_637_, lean_object* v_k_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Int_Internal_Linear_Poly_mul(v_p_637_, v_k_638_);
lean_dec(v_k_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object* v_fuel_640_, lean_object* v_h__1_641_, lean_object* v_h__2_642_){
_start:
{
lean_object* v_zero_643_; uint8_t v_isZero_644_; 
v_zero_643_ = lean_unsigned_to_nat(0u);
v_isZero_644_ = lean_nat_dec_eq(v_fuel_640_, v_zero_643_);
if (v_isZero_644_ == 1)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_h__2_642_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_apply_1(v_h__1_641_, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_one_647_; lean_object* v_n_648_; lean_object* v___x_649_; 
lean_dec(v_h__1_641_);
v_one_647_ = lean_unsigned_to_nat(1u);
v_n_648_ = lean_nat_sub(v_fuel_640_, v_one_647_);
v___x_649_ = lean_apply_1(v_h__2_642_, v_n_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object* v_fuel_650_, lean_object* v_h__1_651_, lean_object* v_h__2_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(v_fuel_650_, v_h__1_651_, v_h__2_652_);
lean_dec(v_fuel_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(lean_object* v_motive_654_, lean_object* v_fuel_655_, lean_object* v_h__1_656_, lean_object* v_h__2_657_){
_start:
{
lean_object* v_zero_658_; uint8_t v_isZero_659_; 
v_zero_658_ = lean_unsigned_to_nat(0u);
v_isZero_659_ = lean_nat_dec_eq(v_fuel_655_, v_zero_658_);
if (v_isZero_659_ == 1)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_h__2_657_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_apply_1(v_h__1_656_, v___x_660_);
return v___x_661_;
}
else
{
lean_object* v_one_662_; lean_object* v_n_663_; lean_object* v___x_664_; 
lean_dec(v_h__1_656_);
v_one_662_ = lean_unsigned_to_nat(1u);
v_n_663_ = lean_nat_sub(v_fuel_655_, v_one_662_);
v___x_664_ = lean_apply_1(v_h__2_657_, v_n_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object* v_motive_665_, lean_object* v_fuel_666_, lean_object* v_h__1_667_, lean_object* v_h__2_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(v_motive_665_, v_fuel_666_, v_h__1_667_, v_h__2_668_);
lean_dec(v_fuel_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object* v_p_u2081_670_, lean_object* v_p_u2082_671_, lean_object* v_h__1_672_, lean_object* v_h__2_673_, lean_object* v_h__3_674_, lean_object* v_h__4_675_){
_start:
{
if (lean_obj_tag(v_p_u2081_670_) == 0)
{
lean_dec(v_h__4_675_);
lean_dec(v_h__3_674_);
if (lean_obj_tag(v_p_u2082_671_) == 0)
{
lean_object* v_k_676_; lean_object* v_k_677_; lean_object* v___x_678_; 
lean_dec(v_h__2_673_);
v_k_676_ = lean_ctor_get(v_p_u2081_670_, 0);
lean_inc(v_k_676_);
lean_dec_ref_known(v_p_u2081_670_, 1);
v_k_677_ = lean_ctor_get(v_p_u2082_671_, 0);
lean_inc(v_k_677_);
lean_dec_ref_known(v_p_u2082_671_, 1);
v___x_678_ = lean_apply_2(v_h__1_672_, v_k_676_, v_k_677_);
return v___x_678_;
}
else
{
lean_object* v_k_679_; lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v_p_682_; lean_object* v___x_683_; 
lean_dec(v_h__1_672_);
v_k_679_ = lean_ctor_get(v_p_u2081_670_, 0);
lean_inc(v_k_679_);
lean_dec_ref_known(v_p_u2081_670_, 1);
v_k_680_ = lean_ctor_get(v_p_u2082_671_, 0);
lean_inc(v_k_680_);
v_v_681_ = lean_ctor_get(v_p_u2082_671_, 1);
lean_inc(v_v_681_);
v_p_682_ = lean_ctor_get(v_p_u2082_671_, 2);
lean_inc_ref(v_p_682_);
lean_dec_ref_known(v_p_u2082_671_, 3);
v___x_683_ = lean_apply_4(v_h__2_673_, v_k_679_, v_k_680_, v_v_681_, v_p_682_);
return v___x_683_;
}
}
else
{
lean_dec(v_h__2_673_);
lean_dec(v_h__1_672_);
if (lean_obj_tag(v_p_u2082_671_) == 0)
{
lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_p_686_; lean_object* v_k_687_; lean_object* v___x_688_; 
lean_dec(v_h__4_675_);
v_k_684_ = lean_ctor_get(v_p_u2081_670_, 0);
lean_inc(v_k_684_);
v_v_685_ = lean_ctor_get(v_p_u2081_670_, 1);
lean_inc(v_v_685_);
v_p_686_ = lean_ctor_get(v_p_u2081_670_, 2);
lean_inc_ref(v_p_686_);
lean_dec_ref_known(v_p_u2081_670_, 3);
v_k_687_ = lean_ctor_get(v_p_u2082_671_, 0);
lean_inc(v_k_687_);
lean_dec_ref_known(v_p_u2082_671_, 1);
v___x_688_ = lean_apply_4(v_h__3_674_, v_k_684_, v_v_685_, v_p_686_, v_k_687_);
return v___x_688_;
}
else
{
lean_object* v_k_689_; lean_object* v_v_690_; lean_object* v_p_691_; lean_object* v_k_692_; lean_object* v_v_693_; lean_object* v_p_694_; lean_object* v___x_695_; 
lean_dec(v_h__3_674_);
v_k_689_ = lean_ctor_get(v_p_u2081_670_, 0);
lean_inc(v_k_689_);
v_v_690_ = lean_ctor_get(v_p_u2081_670_, 1);
lean_inc(v_v_690_);
v_p_691_ = lean_ctor_get(v_p_u2081_670_, 2);
lean_inc_ref(v_p_691_);
lean_dec_ref_known(v_p_u2081_670_, 3);
v_k_692_ = lean_ctor_get(v_p_u2082_671_, 0);
lean_inc(v_k_692_);
v_v_693_ = lean_ctor_get(v_p_u2082_671_, 1);
lean_inc(v_v_693_);
v_p_694_ = lean_ctor_get(v_p_u2082_671_, 2);
lean_inc_ref(v_p_694_);
lean_dec_ref_known(v_p_u2082_671_, 3);
v___x_695_ = lean_apply_6(v_h__4_675_, v_k_689_, v_v_690_, v_p_691_, v_k_692_, v_v_693_, v_p_694_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter(lean_object* v_motive_696_, lean_object* v_p_u2081_697_, lean_object* v_p_u2082_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_, lean_object* v_h__3_701_, lean_object* v_h__4_702_){
_start:
{
if (lean_obj_tag(v_p_u2081_697_) == 0)
{
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
if (lean_obj_tag(v_p_u2082_698_) == 0)
{
lean_object* v_k_703_; lean_object* v_k_704_; lean_object* v___x_705_; 
lean_dec(v_h__2_700_);
v_k_703_ = lean_ctor_get(v_p_u2081_697_, 0);
lean_inc(v_k_703_);
lean_dec_ref_known(v_p_u2081_697_, 1);
v_k_704_ = lean_ctor_get(v_p_u2082_698_, 0);
lean_inc(v_k_704_);
lean_dec_ref_known(v_p_u2082_698_, 1);
v___x_705_ = lean_apply_2(v_h__1_699_, v_k_703_, v_k_704_);
return v___x_705_;
}
else
{
lean_object* v_k_706_; lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_p_709_; lean_object* v___x_710_; 
lean_dec(v_h__1_699_);
v_k_706_ = lean_ctor_get(v_p_u2081_697_, 0);
lean_inc(v_k_706_);
lean_dec_ref_known(v_p_u2081_697_, 1);
v_k_707_ = lean_ctor_get(v_p_u2082_698_, 0);
lean_inc(v_k_707_);
v_v_708_ = lean_ctor_get(v_p_u2082_698_, 1);
lean_inc(v_v_708_);
v_p_709_ = lean_ctor_get(v_p_u2082_698_, 2);
lean_inc_ref(v_p_709_);
lean_dec_ref_known(v_p_u2082_698_, 3);
v___x_710_ = lean_apply_4(v_h__2_700_, v_k_706_, v_k_707_, v_v_708_, v_p_709_);
return v___x_710_;
}
}
else
{
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
if (lean_obj_tag(v_p_u2082_698_) == 0)
{
lean_object* v_k_711_; lean_object* v_v_712_; lean_object* v_p_713_; lean_object* v_k_714_; lean_object* v___x_715_; 
lean_dec(v_h__4_702_);
v_k_711_ = lean_ctor_get(v_p_u2081_697_, 0);
lean_inc(v_k_711_);
v_v_712_ = lean_ctor_get(v_p_u2081_697_, 1);
lean_inc(v_v_712_);
v_p_713_ = lean_ctor_get(v_p_u2081_697_, 2);
lean_inc_ref(v_p_713_);
lean_dec_ref_known(v_p_u2081_697_, 3);
v_k_714_ = lean_ctor_get(v_p_u2082_698_, 0);
lean_inc(v_k_714_);
lean_dec_ref_known(v_p_u2082_698_, 1);
v___x_715_ = lean_apply_4(v_h__3_701_, v_k_711_, v_v_712_, v_p_713_, v_k_714_);
return v___x_715_;
}
else
{
lean_object* v_k_716_; lean_object* v_v_717_; lean_object* v_p_718_; lean_object* v_k_719_; lean_object* v_v_720_; lean_object* v_p_721_; lean_object* v___x_722_; 
lean_dec(v_h__3_701_);
v_k_716_ = lean_ctor_get(v_p_u2081_697_, 0);
lean_inc(v_k_716_);
v_v_717_ = lean_ctor_get(v_p_u2081_697_, 1);
lean_inc(v_v_717_);
v_p_718_ = lean_ctor_get(v_p_u2081_697_, 2);
lean_inc_ref(v_p_718_);
lean_dec_ref_known(v_p_u2081_697_, 3);
v_k_719_ = lean_ctor_get(v_p_u2082_698_, 0);
lean_inc(v_k_719_);
v_v_720_ = lean_ctor_get(v_p_u2082_698_, 1);
lean_inc(v_v_720_);
v_p_721_ = lean_ctor_get(v_p_u2082_698_, 2);
lean_inc_ref(v_p_721_);
lean_dec_ref_known(v_p_u2082_698_, 3);
v___x_722_ = lean_apply_6(v_h__4_702_, v_k_716_, v_v_717_, v_p_718_, v_k_719_, v_v_720_, v_p_721_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_denote_match__1_splitter___redArg(lean_object* v_x_723_, lean_object* v_h__1_724_, lean_object* v_h__2_725_, lean_object* v_h__3_726_, lean_object* v_h__4_727_, lean_object* v_h__5_728_, lean_object* v_h__6_729_, lean_object* v_h__7_730_){
_start:
{
switch(lean_obj_tag(v_x_723_))
{
case 0:
{
lean_object* v_v_731_; lean_object* v___x_732_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_v_731_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_v_731_);
lean_dec_ref_known(v_x_723_, 1);
v___x_732_ = lean_apply_1(v_h__4_727_, v_v_731_);
return v___x_732_;
}
case 1:
{
lean_object* v_i_733_; lean_object* v___x_734_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_i_733_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_i_733_);
lean_dec_ref_known(v_x_723_, 1);
v___x_734_ = lean_apply_1(v_h__5_728_, v_i_733_);
return v___x_734_;
}
case 2:
{
lean_object* v_a_735_; lean_object* v_b_736_; lean_object* v___x_737_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
v_a_735_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_735_);
v_b_736_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_b_736_);
lean_dec_ref_known(v_x_723_, 2);
v___x_737_ = lean_apply_2(v_h__1_724_, v_a_735_, v_b_736_);
return v___x_737_;
}
case 3:
{
lean_object* v_a_738_; lean_object* v_b_739_; lean_object* v___x_740_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__1_724_);
v_a_738_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_738_);
v_b_739_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_b_739_);
lean_dec_ref_known(v_x_723_, 2);
v___x_740_ = lean_apply_2(v_h__2_725_, v_a_738_, v_b_739_);
return v___x_740_;
}
case 4:
{
lean_object* v_a_741_; lean_object* v___x_742_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_a_741_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_741_);
lean_dec_ref_known(v_x_723_, 1);
v___x_742_ = lean_apply_1(v_h__3_726_, v_a_741_);
return v___x_742_;
}
case 5:
{
lean_object* v_k_743_; lean_object* v_a_744_; lean_object* v___x_745_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_k_743_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_k_743_);
v_a_744_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_a_744_);
lean_dec_ref_known(v_x_723_, 2);
v___x_745_ = lean_apply_2(v_h__6_729_, v_k_743_, v_a_744_);
return v___x_745_;
}
default: 
{
lean_object* v_a_746_; lean_object* v_k_747_; lean_object* v___x_748_; 
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_a_746_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_746_);
v_k_747_ = lean_ctor_get(v_x_723_, 1);
lean_inc(v_k_747_);
lean_dec_ref_known(v_x_723_, 2);
v___x_748_ = lean_apply_2(v_h__7_730_, v_a_746_, v_k_747_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_denote_match__1_splitter(lean_object* v_motive_749_, lean_object* v_x_750_, lean_object* v_h__1_751_, lean_object* v_h__2_752_, lean_object* v_h__3_753_, lean_object* v_h__4_754_, lean_object* v_h__5_755_, lean_object* v_h__6_756_, lean_object* v_h__7_757_){
_start:
{
switch(lean_obj_tag(v_x_750_))
{
case 0:
{
lean_object* v_v_758_; lean_object* v___x_759_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_v_758_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_v_758_);
lean_dec_ref_known(v_x_750_, 1);
v___x_759_ = lean_apply_1(v_h__4_754_, v_v_758_);
return v___x_759_;
}
case 1:
{
lean_object* v_i_760_; lean_object* v___x_761_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_i_760_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_i_760_);
lean_dec_ref_known(v_x_750_, 1);
v___x_761_ = lean_apply_1(v_h__5_755_, v_i_760_);
return v___x_761_;
}
case 2:
{
lean_object* v_a_762_; lean_object* v_b_763_; lean_object* v___x_764_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
v_a_762_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_762_);
v_b_763_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_b_763_);
lean_dec_ref_known(v_x_750_, 2);
v___x_764_ = lean_apply_2(v_h__1_751_, v_a_762_, v_b_763_);
return v___x_764_;
}
case 3:
{
lean_object* v_a_765_; lean_object* v_b_766_; lean_object* v___x_767_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__1_751_);
v_a_765_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_765_);
v_b_766_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_b_766_);
lean_dec_ref_known(v_x_750_, 2);
v___x_767_ = lean_apply_2(v_h__2_752_, v_a_765_, v_b_766_);
return v___x_767_;
}
case 4:
{
lean_object* v_a_768_; lean_object* v___x_769_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_a_768_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_768_);
lean_dec_ref_known(v_x_750_, 1);
v___x_769_ = lean_apply_1(v_h__3_753_, v_a_768_);
return v___x_769_;
}
case 5:
{
lean_object* v_k_770_; lean_object* v_a_771_; lean_object* v___x_772_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_k_770_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_k_770_);
v_a_771_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_a_771_);
lean_dec_ref_known(v_x_750_, 2);
v___x_772_ = lean_apply_2(v_h__6_756_, v_k_770_, v_a_771_);
return v___x_772_;
}
default: 
{
lean_object* v_a_773_; lean_object* v_k_774_; lean_object* v___x_775_; 
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_a_773_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_773_);
v_k_774_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_k_774_);
lean_dec_ref_known(v_x_750_, 2);
v___x_775_ = lean_apply_2(v_h__7_757_, v_a_773_, v_k_774_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* v_x_776_, lean_object* v_h__1_777_, lean_object* v_h__2_778_, lean_object* v_h__3_779_, lean_object* v_h__4_780_, lean_object* v_h__5_781_, lean_object* v_h__6_782_, lean_object* v_h__7_783_){
_start:
{
switch(lean_obj_tag(v_x_776_))
{
case 0:
{
lean_object* v_v_784_; lean_object* v___x_785_; 
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
v_v_784_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_v_784_);
lean_dec_ref_known(v_x_776_, 1);
v___x_785_ = lean_apply_1(v_h__1_777_, v_v_784_);
return v___x_785_;
}
case 1:
{
lean_object* v_i_786_; lean_object* v___x_787_; 
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__1_777_);
v_i_786_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_i_786_);
lean_dec_ref_known(v_x_776_, 1);
v___x_787_ = lean_apply_1(v_h__2_778_, v_i_786_);
return v___x_787_;
}
case 2:
{
lean_object* v_a_788_; lean_object* v_b_789_; lean_object* v___x_790_; 
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_a_788_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_a_788_);
v_b_789_ = lean_ctor_get(v_x_776_, 1);
lean_inc_ref(v_b_789_);
lean_dec_ref_known(v_x_776_, 2);
v___x_790_ = lean_apply_2(v_h__3_779_, v_a_788_, v_b_789_);
return v___x_790_;
}
case 3:
{
lean_object* v_a_791_; lean_object* v_b_792_; lean_object* v___x_793_; 
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_a_791_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_a_791_);
v_b_792_ = lean_ctor_get(v_x_776_, 1);
lean_inc_ref(v_b_792_);
lean_dec_ref_known(v_x_776_, 2);
v___x_793_ = lean_apply_2(v_h__4_780_, v_a_791_, v_b_792_);
return v___x_793_;
}
case 4:
{
lean_object* v_a_794_; lean_object* v___x_795_; 
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_a_794_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_a_794_);
lean_dec_ref_known(v_x_776_, 1);
v___x_795_ = lean_apply_1(v_h__7_783_, v_a_794_);
return v___x_795_;
}
case 5:
{
lean_object* v_k_796_; lean_object* v_a_797_; lean_object* v___x_798_; 
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_k_796_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_k_796_);
v_a_797_ = lean_ctor_get(v_x_776_, 1);
lean_inc_ref(v_a_797_);
lean_dec_ref_known(v_x_776_, 2);
v___x_798_ = lean_apply_2(v_h__5_781_, v_k_796_, v_a_797_);
return v___x_798_;
}
default: 
{
lean_object* v_a_799_; lean_object* v_k_800_; lean_object* v___x_801_; 
lean_dec(v_h__7_783_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_a_799_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_a_799_);
v_k_800_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_k_800_);
lean_dec_ref_known(v_x_776_, 2);
v___x_801_ = lean_apply_2(v_h__6_782_, v_a_799_, v_k_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* v_motive_802_, lean_object* v_x_803_, lean_object* v_h__1_804_, lean_object* v_h__2_805_, lean_object* v_h__3_806_, lean_object* v_h__4_807_, lean_object* v_h__5_808_, lean_object* v_h__6_809_, lean_object* v_h__7_810_){
_start:
{
switch(lean_obj_tag(v_x_803_))
{
case 0:
{
lean_object* v_v_811_; lean_object* v___x_812_; 
lean_dec(v_h__7_810_);
lean_dec(v_h__6_809_);
lean_dec(v_h__5_808_);
lean_dec(v_h__4_807_);
lean_dec(v_h__3_806_);
lean_dec(v_h__2_805_);
v_v_811_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_v_811_);
lean_dec_ref_known(v_x_803_, 1);
v___x_812_ = lean_apply_1(v_h__1_804_, v_v_811_);
return v___x_812_;
}
case 1:
{
lean_object* v_i_813_; lean_object* v___x_814_; 
lean_dec(v_h__7_810_);
lean_dec(v_h__6_809_);
lean_dec(v_h__5_808_);
lean_dec(v_h__4_807_);
lean_dec(v_h__3_806_);
lean_dec(v_h__1_804_);
v_i_813_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_i_813_);
lean_dec_ref_known(v_x_803_, 1);
v___x_814_ = lean_apply_1(v_h__2_805_, v_i_813_);
return v___x_814_;
}
case 2:
{
lean_object* v_a_815_; lean_object* v_b_816_; lean_object* v___x_817_; 
lean_dec(v_h__7_810_);
lean_dec(v_h__6_809_);
lean_dec(v_h__5_808_);
lean_dec(v_h__4_807_);
lean_dec(v_h__2_805_);
lean_dec(v_h__1_804_);
v_a_815_ = lean_ctor_get(v_x_803_, 0);
lean_inc_ref(v_a_815_);
v_b_816_ = lean_ctor_get(v_x_803_, 1);
lean_inc_ref(v_b_816_);
lean_dec_ref_known(v_x_803_, 2);
v___x_817_ = lean_apply_2(v_h__3_806_, v_a_815_, v_b_816_);
return v___x_817_;
}
case 3:
{
lean_object* v_a_818_; lean_object* v_b_819_; lean_object* v___x_820_; 
lean_dec(v_h__7_810_);
lean_dec(v_h__6_809_);
lean_dec(v_h__5_808_);
lean_dec(v_h__3_806_);
lean_dec(v_h__2_805_);
lean_dec(v_h__1_804_);
v_a_818_ = lean_ctor_get(v_x_803_, 0);
lean_inc_ref(v_a_818_);
v_b_819_ = lean_ctor_get(v_x_803_, 1);
lean_inc_ref(v_b_819_);
lean_dec_ref_known(v_x_803_, 2);
v___x_820_ = lean_apply_2(v_h__4_807_, v_a_818_, v_b_819_);
return v___x_820_;
}
case 4:
{
lean_object* v_a_821_; lean_object* v___x_822_; 
lean_dec(v_h__6_809_);
lean_dec(v_h__5_808_);
lean_dec(v_h__4_807_);
lean_dec(v_h__3_806_);
lean_dec(v_h__2_805_);
lean_dec(v_h__1_804_);
v_a_821_ = lean_ctor_get(v_x_803_, 0);
lean_inc_ref(v_a_821_);
lean_dec_ref_known(v_x_803_, 1);
v___x_822_ = lean_apply_1(v_h__7_810_, v_a_821_);
return v___x_822_;
}
case 5:
{
lean_object* v_k_823_; lean_object* v_a_824_; lean_object* v___x_825_; 
lean_dec(v_h__7_810_);
lean_dec(v_h__6_809_);
lean_dec(v_h__4_807_);
lean_dec(v_h__3_806_);
lean_dec(v_h__2_805_);
lean_dec(v_h__1_804_);
v_k_823_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_k_823_);
v_a_824_ = lean_ctor_get(v_x_803_, 1);
lean_inc_ref(v_a_824_);
lean_dec_ref_known(v_x_803_, 2);
v___x_825_ = lean_apply_2(v_h__5_808_, v_k_823_, v_a_824_);
return v___x_825_;
}
default: 
{
lean_object* v_a_826_; lean_object* v_k_827_; lean_object* v___x_828_; 
lean_dec(v_h__7_810_);
lean_dec(v_h__5_808_);
lean_dec(v_h__4_807_);
lean_dec(v_h__3_806_);
lean_dec(v_h__2_805_);
lean_dec(v_h__1_804_);
v_a_826_ = lean_ctor_get(v_x_803_, 0);
lean_inc_ref(v_a_826_);
v_k_827_ = lean_ctor_get(v_x_803_, 1);
lean_inc(v_k_827_);
lean_dec_ref_known(v_x_803_, 2);
v___x_828_ = lean_apply_2(v_h__6_809_, v_a_826_, v_k_827_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object* v_p_829_){
_start:
{
if (lean_obj_tag(v_p_829_) == 0)
{
lean_object* v_k_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_k_830_ = lean_ctor_get(v_p_829_, 0);
v___x_831_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_832_ = lean_int_dec_eq(v_k_830_, v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
v___x_833_ = 1;
return v___x_833_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = 0;
return v___x_834_;
}
}
else
{
uint8_t v___x_835_; 
v___x_835_ = 0;
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatEq___boxed(lean_object* v_p_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l_Int_Internal_Linear_Poly_isUnsatEq(v_p_836_);
lean_dec_ref(v_p_836_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object* v_p_839_){
_start:
{
if (lean_obj_tag(v_p_839_) == 0)
{
lean_object* v_k_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_k_840_ = lean_ctor_get(v_p_839_, 0);
v___x_841_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_842_ = lean_int_dec_eq(v_k_840_, v___x_841_);
return v___x_842_;
}
else
{
uint8_t v___x_843_; 
v___x_843_ = 0;
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidEq___boxed(lean_object* v_p_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Int_Internal_Linear_Poly_isValidEq(v_p_844_);
lean_dec_ref(v_p_844_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* v_p_847_, lean_object* v_h__1_848_, lean_object* v_h__2_849_){
_start:
{
if (lean_obj_tag(v_p_847_) == 0)
{
lean_object* v_k_850_; lean_object* v___x_851_; 
lean_dec(v_h__2_849_);
v_k_850_ = lean_ctor_get(v_p_847_, 0);
lean_inc(v_k_850_);
lean_dec_ref_known(v_p_847_, 1);
v___x_851_ = lean_apply_1(v_h__1_848_, v_k_850_);
return v___x_851_;
}
else
{
lean_object* v___x_852_; 
lean_dec(v_h__1_848_);
v___x_852_ = lean_apply_2(v_h__2_849_, v_p_847_, lean_box(0));
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* v_motive_853_, lean_object* v_p_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_){
_start:
{
if (lean_obj_tag(v_p_854_) == 0)
{
lean_object* v_k_857_; lean_object* v___x_858_; 
lean_dec(v_h__2_856_);
v_k_857_ = lean_ctor_get(v_p_854_, 0);
lean_inc(v_k_857_);
lean_dec_ref_known(v_p_854_, 1);
v___x_858_ = lean_apply_1(v_h__1_855_, v_k_857_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; 
lean_dec(v_h__1_855_);
v___x_859_ = lean_apply_2(v_h__2_856_, v_p_854_, lean_box(0));
return v___x_859_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object* v_p_860_){
_start:
{
if (lean_obj_tag(v_p_860_) == 0)
{
lean_object* v_k_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_k_861_ = lean_ctor_get(v_p_860_, 0);
v___x_862_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_863_ = lean_int_dec_lt(v___x_862_, v_k_861_);
return v___x_863_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = 0;
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatLe___boxed(lean_object* v_p_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_865_);
lean_dec_ref(v_p_865_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object* v_p_868_){
_start:
{
if (lean_obj_tag(v_p_868_) == 0)
{
lean_object* v_k_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_k_869_ = lean_ctor_get(v_p_868_, 0);
v___x_870_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_871_ = lean_int_dec_le(v_k_869_, v___x_870_);
return v___x_871_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = 0;
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidLe___boxed(lean_object* v_p_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Int_Internal_Linear_Poly_isValidLe(v_p_873_);
lean_dec_ref(v_p_873_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(lean_object* v_a_876_, lean_object* v_b_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = l_Int_gcd(v_a_876_, v_b_877_);
v___x_879_ = lean_nat_to_int(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd___boxed(lean_object* v_a_880_, lean_object* v_b_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(v_a_880_, v_b_881_);
lean_dec(v_b_881_);
lean_dec(v_a_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
return v_x_884_;
}
else
{
lean_object* v_k_885_; lean_object* v_p_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_k_885_ = lean_ctor_get(v_x_883_, 0);
v_p_886_ = lean_ctor_get(v_x_883_, 2);
v___x_887_ = l_Int_gcd(v_k_885_, v_x_884_);
lean_dec(v_x_884_);
v___x_888_ = lean_nat_to_int(v___x_887_);
v_x_883_ = v_p_886_;
v_x_884_ = v___x_888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs___boxed(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_x_890_, v_x_891_);
lean_dec_ref(v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_h__1_895_, lean_object* v_h__2_896_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_k_897_; lean_object* v___x_898_; 
lean_dec(v_h__2_896_);
v_k_897_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_k_897_);
lean_dec_ref_known(v_x_893_, 1);
v___x_898_ = lean_apply_2(v_h__1_895_, v_k_897_, v_x_894_);
return v___x_898_;
}
else
{
lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_p_901_; lean_object* v___x_902_; 
lean_dec(v_h__1_895_);
v_k_899_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_k_899_);
v_v_900_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_v_900_);
v_p_901_ = lean_ctor_get(v_x_893_, 2);
lean_inc_ref(v_p_901_);
lean_dec_ref_known(v_x_893_, 3);
v___x_902_ = lean_apply_4(v_h__2_896_, v_k_899_, v_v_900_, v_p_901_, v_x_894_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object* v_motive_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v_k_908_; lean_object* v___x_909_; 
lean_dec(v_h__2_907_);
v_k_908_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_k_908_);
lean_dec_ref_known(v_x_904_, 1);
v___x_909_ = lean_apply_2(v_h__1_906_, v_k_908_, v_x_905_);
return v___x_909_;
}
else
{
lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v_p_912_; lean_object* v___x_913_; 
lean_dec(v_h__1_906_);
v_k_910_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_k_910_);
v_v_911_ = lean_ctor_get(v_x_904_, 1);
lean_inc(v_v_911_);
v_p_912_ = lean_ctor_get(v_x_904_, 2);
lean_inc_ref(v_p_912_);
lean_dec_ref_known(v_x_904_, 3);
v___x_913_ = lean_apply_4(v_h__2_907_, v_k_910_, v_v_911_, v_p_912_, v_x_905_);
return v___x_913_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object* v_k_914_, lean_object* v_p_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_916_ = l_Int_Internal_Linear_Poly_getConst(v_p_915_);
v___x_917_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_915_, v_k_914_);
v___x_918_ = lean_int_emod(v___x_916_, v___x_917_);
lean_dec(v___x_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_920_ = lean_int_dec_eq(v___x_918_, v___x_919_);
lean_dec(v___x_918_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
v___x_921_ = 1;
return v___x_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDvd___boxed(lean_object* v_k_923_, lean_object* v_p_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_k_923_, v_p_924_);
lean_dec_ref(v_p_924_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object* v_p_u2081_927_, lean_object* v_p_u2082_928_, lean_object* v_h__1_929_, lean_object* v_h__2_930_){
_start:
{
if (lean_obj_tag(v_p_u2081_927_) == 1)
{
if (lean_obj_tag(v_p_u2082_928_) == 1)
{
lean_object* v_k_931_; lean_object* v_v_932_; lean_object* v_p_933_; lean_object* v_k_934_; lean_object* v_v_935_; lean_object* v_p_936_; lean_object* v___x_937_; 
lean_dec(v_h__2_930_);
v_k_931_ = lean_ctor_get(v_p_u2081_927_, 0);
lean_inc(v_k_931_);
v_v_932_ = lean_ctor_get(v_p_u2081_927_, 1);
lean_inc(v_v_932_);
v_p_933_ = lean_ctor_get(v_p_u2081_927_, 2);
lean_inc_ref(v_p_933_);
lean_dec_ref_known(v_p_u2081_927_, 3);
v_k_934_ = lean_ctor_get(v_p_u2082_928_, 0);
lean_inc(v_k_934_);
v_v_935_ = lean_ctor_get(v_p_u2082_928_, 1);
lean_inc(v_v_935_);
v_p_936_ = lean_ctor_get(v_p_u2082_928_, 2);
lean_inc_ref(v_p_936_);
lean_dec_ref_known(v_p_u2082_928_, 3);
v___x_937_ = lean_apply_6(v_h__1_929_, v_k_931_, v_v_932_, v_p_933_, v_k_934_, v_v_935_, v_p_936_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; 
lean_dec(v_h__1_929_);
v___x_938_ = lean_apply_3(v_h__2_930_, v_p_u2081_927_, v_p_u2082_928_, lean_box(0));
return v___x_938_;
}
}
else
{
lean_object* v___x_939_; 
lean_dec(v_h__1_929_);
v___x_939_ = lean_apply_3(v_h__2_930_, v_p_u2081_927_, v_p_u2082_928_, lean_box(0));
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object* v_motive_940_, lean_object* v_p_u2081_941_, lean_object* v_p_u2082_942_, lean_object* v_h__1_943_, lean_object* v_h__2_944_){
_start:
{
if (lean_obj_tag(v_p_u2081_941_) == 1)
{
if (lean_obj_tag(v_p_u2082_942_) == 1)
{
lean_object* v_k_945_; lean_object* v_v_946_; lean_object* v_p_947_; lean_object* v_k_948_; lean_object* v_v_949_; lean_object* v_p_950_; lean_object* v___x_951_; 
lean_dec(v_h__2_944_);
v_k_945_ = lean_ctor_get(v_p_u2081_941_, 0);
lean_inc(v_k_945_);
v_v_946_ = lean_ctor_get(v_p_u2081_941_, 1);
lean_inc(v_v_946_);
v_p_947_ = lean_ctor_get(v_p_u2081_941_, 2);
lean_inc_ref(v_p_947_);
lean_dec_ref_known(v_p_u2081_941_, 3);
v_k_948_ = lean_ctor_get(v_p_u2082_942_, 0);
lean_inc(v_k_948_);
v_v_949_ = lean_ctor_get(v_p_u2082_942_, 1);
lean_inc(v_v_949_);
v_p_950_ = lean_ctor_get(v_p_u2082_942_, 2);
lean_inc_ref(v_p_950_);
lean_dec_ref_known(v_p_u2082_942_, 3);
v___x_951_ = lean_apply_6(v_h__1_943_, v_k_945_, v_v_946_, v_p_947_, v_k_948_, v_v_949_, v_p_950_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; 
lean_dec(v_h__1_943_);
v___x_952_ = lean_apply_3(v_h__2_944_, v_p_u2081_941_, v_p_u2082_942_, lean_box(0));
return v___x_952_;
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v_h__1_943_);
v___x_953_ = lean_apply_3(v_h__2_944_, v_p_u2081_941_, v_p_u2082_942_, lean_box(0));
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object* v_p_954_){
_start:
{
if (lean_obj_tag(v_p_954_) == 1)
{
lean_object* v_k_955_; 
v_k_955_ = lean_ctor_get(v_p_954_, 0);
lean_inc(v_k_955_);
return v_k_955_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff___boxed(lean_object* v_p_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_957_);
lean_dec_ref(v_p_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object* v_p_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_p_959_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
return v___x_961_;
}
else
{
lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v_p_964_; uint8_t v___x_965_; 
v_k_962_ = lean_ctor_get(v_p_959_, 0);
v_v_963_ = lean_ctor_get(v_p_959_, 1);
v_p_964_ = lean_ctor_get(v_p_959_, 2);
v___x_965_ = lean_nat_dec_eq(v_x_960_, v_v_963_);
if (v___x_965_ == 0)
{
v_p_959_ = v_p_964_;
goto _start;
}
else
{
lean_inc(v_k_962_);
return v_k_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff___boxed(lean_object* v_p_967_, lean_object* v_x_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Int_Internal_Linear_Poly_coeff(v_p_967_, v_x_968_);
lean_dec(v_x_968_);
lean_dec_ref(v_p_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_coeff_match__1_splitter___redArg(lean_object* v_p_970_, lean_object* v_h__1_971_, lean_object* v_h__2_972_){
_start:
{
if (lean_obj_tag(v_p_970_) == 0)
{
lean_object* v_k_973_; lean_object* v___x_974_; 
lean_dec(v_h__1_971_);
v_k_973_ = lean_ctor_get(v_p_970_, 0);
lean_inc(v_k_973_);
lean_dec_ref_known(v_p_970_, 1);
v___x_974_ = lean_apply_1(v_h__2_972_, v_k_973_);
return v___x_974_;
}
else
{
lean_object* v_k_975_; lean_object* v_v_976_; lean_object* v_p_977_; lean_object* v___x_978_; 
lean_dec(v_h__2_972_);
v_k_975_ = lean_ctor_get(v_p_970_, 0);
lean_inc(v_k_975_);
v_v_976_ = lean_ctor_get(v_p_970_, 1);
lean_inc(v_v_976_);
v_p_977_ = lean_ctor_get(v_p_970_, 2);
lean_inc_ref(v_p_977_);
lean_dec_ref_known(v_p_970_, 3);
v___x_978_ = lean_apply_3(v_h__1_971_, v_k_975_, v_v_976_, v_p_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_coeff_match__1_splitter(lean_object* v_motive_979_, lean_object* v_p_980_, lean_object* v_h__1_981_, lean_object* v_h__2_982_){
_start:
{
if (lean_obj_tag(v_p_980_) == 0)
{
lean_object* v_k_983_; lean_object* v___x_984_; 
lean_dec(v_h__1_981_);
v_k_983_ = lean_ctor_get(v_p_980_, 0);
lean_inc(v_k_983_);
lean_dec_ref_known(v_p_980_, 1);
v___x_984_ = lean_apply_1(v_h__2_982_, v_k_983_);
return v___x_984_;
}
else
{
lean_object* v_k_985_; lean_object* v_v_986_; lean_object* v_p_987_; lean_object* v___x_988_; 
lean_dec(v_h__2_982_);
v_k_985_ = lean_ctor_get(v_p_980_, 0);
lean_inc(v_k_985_);
v_v_986_ = lean_ctor_get(v_p_980_, 1);
lean_inc(v_v_986_);
v_p_987_ = lean_ctor_get(v_p_980_, 2);
lean_inc_ref(v_p_987_);
lean_dec_ref_known(v_p_980_, 3);
v___x_988_ = lean_apply_3(v_h__1_981_, v_k_985_, v_v_986_, v_p_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs(lean_object* v_x_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_nat_abs(v_x_989_);
v___x_991_ = lean_nat_to_int(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs___boxed(lean_object* v_x_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Int_Internal_Linear_abs(v_x_992_);
lean_dec(v_x_992_);
return v_res_993_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDiseq(lean_object* v_p_994_){
_start:
{
if (lean_obj_tag(v_p_994_) == 0)
{
lean_object* v_k_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_k_995_ = lean_ctor_get(v_p_994_, 0);
v___x_996_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_997_ = lean_int_dec_eq(v_k_995_, v___x_996_);
return v___x_997_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = 0;
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDiseq___boxed(lean_object* v_p_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_Int_Internal_Linear_Poly_isUnsatDiseq(v_p_999_);
lean_dec_ref(v_p_999_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail(lean_object* v_p_1002_){
_start:
{
if (lean_obj_tag(v_p_1002_) == 1)
{
lean_object* v_p_1003_; 
v_p_1003_ = lean_ctor_get(v_p_1002_, 2);
lean_inc_ref(v_p_1003_);
return v_p_1003_;
}
else
{
lean_inc_ref(v_p_1002_);
return v_p_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail___boxed(lean_object* v_p_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Int_Internal_Linear_Poly_tail(v_p_1004_);
lean_dec_ref(v_p_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object* v_p_1006_, lean_object* v_h__1_1007_, lean_object* v_h__2_1008_){
_start:
{
if (lean_obj_tag(v_p_1006_) == 1)
{
lean_object* v_k_1009_; lean_object* v_v_1010_; lean_object* v_p_1011_; lean_object* v___x_1012_; 
lean_dec(v_h__2_1008_);
v_k_1009_ = lean_ctor_get(v_p_1006_, 0);
lean_inc(v_k_1009_);
v_v_1010_ = lean_ctor_get(v_p_1006_, 1);
lean_inc(v_v_1010_);
v_p_1011_ = lean_ctor_get(v_p_1006_, 2);
lean_inc_ref(v_p_1011_);
lean_dec_ref_known(v_p_1006_, 3);
v___x_1012_ = lean_apply_3(v_h__1_1007_, v_k_1009_, v_v_1010_, v_p_1011_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
lean_dec(v_h__1_1007_);
v___x_1013_ = lean_apply_2(v_h__2_1008_, v_p_1006_, lean_box(0));
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter(lean_object* v_motive_1014_, lean_object* v_p_1015_, lean_object* v_h__1_1016_, lean_object* v_h__2_1017_){
_start:
{
if (lean_obj_tag(v_p_1015_) == 1)
{
lean_object* v_k_1018_; lean_object* v_v_1019_; lean_object* v_p_1020_; lean_object* v___x_1021_; 
lean_dec(v_h__2_1017_);
v_k_1018_ = lean_ctor_get(v_p_1015_, 0);
lean_inc(v_k_1018_);
v_v_1019_ = lean_ctor_get(v_p_1015_, 1);
lean_inc(v_v_1019_);
v_p_1020_ = lean_ctor_get(v_p_1015_, 2);
lean_inc_ref(v_p_1020_);
lean_dec_ref_known(v_p_1015_, 3);
v___x_1021_ = lean_apply_3(v_h__1_1016_, v_k_1018_, v_v_1019_, v_p_1020_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; 
lean_dec(v_h__1_1016_);
v___x_1022_ = lean_apply_2(v_h__2_1017_, v_p_1015_, lean_box(0));
return v___x_1022_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnAdd(lean_object* v_p_1023_, lean_object* v_k_1024_){
_start:
{
if (lean_obj_tag(v_p_1023_) == 0)
{
uint8_t v___x_1025_; 
lean_dec_ref_known(v_p_1023_, 1);
lean_dec_ref(v_k_1024_);
v___x_1025_ = 0;
return v___x_1025_;
}
else
{
lean_object* v_a_1026_; lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_a_1026_ = lean_ctor_get(v_p_1023_, 0);
lean_inc(v_a_1026_);
v_a_1027_ = lean_ctor_get(v_p_1023_, 1);
lean_inc(v_a_1027_);
v_a_1028_ = lean_ctor_get(v_p_1023_, 2);
lean_inc_ref(v_a_1028_);
lean_dec_ref_known(v_p_1023_, 3);
v___x_1029_ = lean_apply_3(v_k_1024_, v_a_1026_, v_a_1027_, v_a_1028_);
v___x_1030_ = lean_unbox(v___x_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnAdd___boxed(lean_object* v_p_1031_, lean_object* v_k_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Int_Internal_Linear_Poly_casesOnAdd(v_p_1031_, v_k_1032_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnNum(lean_object* v_p_1035_, lean_object* v_k_1036_){
_start:
{
if (lean_obj_tag(v_p_1035_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_a_1037_ = lean_ctor_get(v_p_1035_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v_p_1035_, 1);
v___x_1038_ = lean_apply_1(v_k_1036_, v_a_1037_);
v___x_1039_ = lean_unbox(v___x_1038_);
return v___x_1039_;
}
else
{
uint8_t v___x_1040_; 
lean_dec_ref_known(v_p_1035_, 3);
lean_dec_ref(v_k_1036_);
v___x_1040_ = 0;
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnNum___boxed(lean_object* v_p_1041_, lean_object* v_k_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Int_Internal_Linear_Poly_casesOnNum(v_p_1041_, v_k_1042_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_emod__le__cert(lean_object* v_y_1045_, lean_object* v_n_1046_){
_start:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_1048_ = lean_int_dec_eq(v_y_1045_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1049_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_1050_ = lean_nat_abs(v_y_1045_);
v___x_1051_ = lean_nat_to_int(v___x_1050_);
v___x_1052_ = lean_int_sub(v___x_1049_, v___x_1051_);
lean_dec(v___x_1051_);
v___x_1053_ = lean_int_dec_eq(v_n_1046_, v___x_1052_);
lean_dec(v___x_1052_);
return v___x_1053_;
}
else
{
uint8_t v___x_1054_; 
v___x_1054_ = 0;
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_emod__le__cert___boxed(lean_object* v_y_1055_, lean_object* v_n_1056_){
_start:
{
uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = l_Int_Internal_Linear_emod__le__cert(v_y_1055_, v_n_1056_);
lean_dec(v_n_1056_);
lean_dec(v_y_1055_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_le__of__le__cert(lean_object* v_p_u2081_1059_, lean_object* v_p_u2082_1060_){
_start:
{
if (lean_obj_tag(v_p_u2081_1059_) == 0)
{
if (lean_obj_tag(v_p_u2082_1060_) == 0)
{
lean_object* v_k_1061_; lean_object* v_k_1062_; uint8_t v___x_1063_; 
v_k_1061_ = lean_ctor_get(v_p_u2081_1059_, 0);
v_k_1062_ = lean_ctor_get(v_p_u2082_1060_, 0);
v___x_1063_ = lean_int_dec_le(v_k_1062_, v_k_1061_);
return v___x_1063_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = 0;
return v___x_1064_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1060_) == 0)
{
uint8_t v___x_1065_; 
v___x_1065_ = 0;
return v___x_1065_;
}
else
{
lean_object* v_k_1066_; lean_object* v_v_1067_; lean_object* v_p_1068_; lean_object* v_k_1069_; lean_object* v_v_1070_; lean_object* v_p_1071_; uint8_t v___x_1072_; 
v_k_1066_ = lean_ctor_get(v_p_u2081_1059_, 0);
v_v_1067_ = lean_ctor_get(v_p_u2081_1059_, 1);
v_p_1068_ = lean_ctor_get(v_p_u2081_1059_, 2);
v_k_1069_ = lean_ctor_get(v_p_u2082_1060_, 0);
v_v_1070_ = lean_ctor_get(v_p_u2082_1060_, 1);
v_p_1071_ = lean_ctor_get(v_p_u2082_1060_, 2);
v___x_1072_ = lean_int_dec_eq(v_k_1066_, v_k_1069_);
if (v___x_1072_ == 0)
{
return v___x_1072_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_eq(v_v_1067_, v_v_1070_);
if (v___x_1073_ == 0)
{
return v___x_1073_;
}
else
{
v_p_u2081_1059_ = v_p_1068_;
v_p_u2082_1060_ = v_p_1071_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_le__of__le__cert___boxed(lean_object* v_p_u2081_1075_, lean_object* v_p_u2082_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Int_Internal_Linear_le__of__le__cert(v_p_u2081_1075_, v_p_u2082_1076_);
lean_dec_ref(v_p_u2082_1076_);
lean_dec_ref(v_p_u2081_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object* v_p_u2081_1079_, lean_object* v_p_u2082_1080_, lean_object* v_h__1_1081_, lean_object* v_h__2_1082_, lean_object* v_h__3_1083_, lean_object* v_h__4_1084_){
_start:
{
if (lean_obj_tag(v_p_u2081_1079_) == 0)
{
lean_dec(v_h__4_1084_);
lean_dec(v_h__1_1081_);
if (lean_obj_tag(v_p_u2082_1080_) == 0)
{
lean_object* v_k_1085_; lean_object* v_k_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__2_1082_);
v_k_1085_ = lean_ctor_get(v_p_u2081_1079_, 0);
lean_inc(v_k_1085_);
lean_dec_ref_known(v_p_u2081_1079_, 1);
v_k_1086_ = lean_ctor_get(v_p_u2082_1080_, 0);
lean_inc(v_k_1086_);
lean_dec_ref_known(v_p_u2082_1080_, 1);
v___x_1087_ = lean_apply_2(v_h__3_1083_, v_k_1085_, v_k_1086_);
return v___x_1087_;
}
else
{
lean_object* v_k_1088_; lean_object* v_k_1089_; lean_object* v_v_1090_; lean_object* v_p_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__3_1083_);
v_k_1088_ = lean_ctor_get(v_p_u2081_1079_, 0);
lean_inc(v_k_1088_);
lean_dec_ref_known(v_p_u2081_1079_, 1);
v_k_1089_ = lean_ctor_get(v_p_u2082_1080_, 0);
lean_inc(v_k_1089_);
v_v_1090_ = lean_ctor_get(v_p_u2082_1080_, 1);
lean_inc(v_v_1090_);
v_p_1091_ = lean_ctor_get(v_p_u2082_1080_, 2);
lean_inc_ref(v_p_1091_);
lean_dec_ref_known(v_p_u2082_1080_, 3);
v___x_1092_ = lean_apply_4(v_h__2_1082_, v_k_1088_, v_k_1089_, v_v_1090_, v_p_1091_);
return v___x_1092_;
}
}
else
{
lean_dec(v_h__3_1083_);
lean_dec(v_h__2_1082_);
if (lean_obj_tag(v_p_u2082_1080_) == 0)
{
lean_object* v_k_1093_; lean_object* v_v_1094_; lean_object* v_p_1095_; lean_object* v_k_1096_; lean_object* v___x_1097_; 
lean_dec(v_h__4_1084_);
v_k_1093_ = lean_ctor_get(v_p_u2081_1079_, 0);
lean_inc(v_k_1093_);
v_v_1094_ = lean_ctor_get(v_p_u2081_1079_, 1);
lean_inc(v_v_1094_);
v_p_1095_ = lean_ctor_get(v_p_u2081_1079_, 2);
lean_inc_ref(v_p_1095_);
lean_dec_ref_known(v_p_u2081_1079_, 3);
v_k_1096_ = lean_ctor_get(v_p_u2082_1080_, 0);
lean_inc(v_k_1096_);
lean_dec_ref_known(v_p_u2082_1080_, 1);
v___x_1097_ = lean_apply_4(v_h__1_1081_, v_k_1093_, v_v_1094_, v_p_1095_, v_k_1096_);
return v___x_1097_;
}
else
{
lean_object* v_k_1098_; lean_object* v_v_1099_; lean_object* v_p_1100_; lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v_p_1103_; lean_object* v___x_1104_; 
lean_dec(v_h__1_1081_);
v_k_1098_ = lean_ctor_get(v_p_u2081_1079_, 0);
lean_inc(v_k_1098_);
v_v_1099_ = lean_ctor_get(v_p_u2081_1079_, 1);
lean_inc(v_v_1099_);
v_p_1100_ = lean_ctor_get(v_p_u2081_1079_, 2);
lean_inc_ref(v_p_1100_);
lean_dec_ref_known(v_p_u2081_1079_, 3);
v_k_1101_ = lean_ctor_get(v_p_u2082_1080_, 0);
lean_inc(v_k_1101_);
v_v_1102_ = lean_ctor_get(v_p_u2082_1080_, 1);
lean_inc(v_v_1102_);
v_p_1103_ = lean_ctor_get(v_p_u2082_1080_, 2);
lean_inc_ref(v_p_1103_);
lean_dec_ref_known(v_p_u2082_1080_, 3);
v___x_1104_ = lean_apply_6(v_h__4_1084_, v_k_1098_, v_v_1099_, v_p_1100_, v_k_1101_, v_v_1102_, v_p_1103_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter(lean_object* v_motive_1105_, lean_object* v_p_u2081_1106_, lean_object* v_p_u2082_1107_, lean_object* v_h__1_1108_, lean_object* v_h__2_1109_, lean_object* v_h__3_1110_, lean_object* v_h__4_1111_){
_start:
{
if (lean_obj_tag(v_p_u2081_1106_) == 0)
{
lean_dec(v_h__4_1111_);
lean_dec(v_h__1_1108_);
if (lean_obj_tag(v_p_u2082_1107_) == 0)
{
lean_object* v_k_1112_; lean_object* v_k_1113_; lean_object* v___x_1114_; 
lean_dec(v_h__2_1109_);
v_k_1112_ = lean_ctor_get(v_p_u2081_1106_, 0);
lean_inc(v_k_1112_);
lean_dec_ref_known(v_p_u2081_1106_, 1);
v_k_1113_ = lean_ctor_get(v_p_u2082_1107_, 0);
lean_inc(v_k_1113_);
lean_dec_ref_known(v_p_u2082_1107_, 1);
v___x_1114_ = lean_apply_2(v_h__3_1110_, v_k_1112_, v_k_1113_);
return v___x_1114_;
}
else
{
lean_object* v_k_1115_; lean_object* v_k_1116_; lean_object* v_v_1117_; lean_object* v_p_1118_; lean_object* v___x_1119_; 
lean_dec(v_h__3_1110_);
v_k_1115_ = lean_ctor_get(v_p_u2081_1106_, 0);
lean_inc(v_k_1115_);
lean_dec_ref_known(v_p_u2081_1106_, 1);
v_k_1116_ = lean_ctor_get(v_p_u2082_1107_, 0);
lean_inc(v_k_1116_);
v_v_1117_ = lean_ctor_get(v_p_u2082_1107_, 1);
lean_inc(v_v_1117_);
v_p_1118_ = lean_ctor_get(v_p_u2082_1107_, 2);
lean_inc_ref(v_p_1118_);
lean_dec_ref_known(v_p_u2082_1107_, 3);
v___x_1119_ = lean_apply_4(v_h__2_1109_, v_k_1115_, v_k_1116_, v_v_1117_, v_p_1118_);
return v___x_1119_;
}
}
else
{
lean_dec(v_h__3_1110_);
lean_dec(v_h__2_1109_);
if (lean_obj_tag(v_p_u2082_1107_) == 0)
{
lean_object* v_k_1120_; lean_object* v_v_1121_; lean_object* v_p_1122_; lean_object* v_k_1123_; lean_object* v___x_1124_; 
lean_dec(v_h__4_1111_);
v_k_1120_ = lean_ctor_get(v_p_u2081_1106_, 0);
lean_inc(v_k_1120_);
v_v_1121_ = lean_ctor_get(v_p_u2081_1106_, 1);
lean_inc(v_v_1121_);
v_p_1122_ = lean_ctor_get(v_p_u2081_1106_, 2);
lean_inc_ref(v_p_1122_);
lean_dec_ref_known(v_p_u2081_1106_, 3);
v_k_1123_ = lean_ctor_get(v_p_u2082_1107_, 0);
lean_inc(v_k_1123_);
lean_dec_ref_known(v_p_u2082_1107_, 1);
v___x_1124_ = lean_apply_4(v_h__1_1108_, v_k_1120_, v_v_1121_, v_p_1122_, v_k_1123_);
return v___x_1124_;
}
else
{
lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v_p_1127_; lean_object* v_k_1128_; lean_object* v_v_1129_; lean_object* v_p_1130_; lean_object* v___x_1131_; 
lean_dec(v_h__1_1108_);
v_k_1125_ = lean_ctor_get(v_p_u2081_1106_, 0);
lean_inc(v_k_1125_);
v_v_1126_ = lean_ctor_get(v_p_u2081_1106_, 1);
lean_inc(v_v_1126_);
v_p_1127_ = lean_ctor_get(v_p_u2081_1106_, 2);
lean_inc_ref(v_p_1127_);
lean_dec_ref_known(v_p_u2081_1106_, 3);
v_k_1128_ = lean_ctor_get(v_p_u2082_1107_, 0);
lean_inc(v_k_1128_);
v_v_1129_ = lean_ctor_get(v_p_u2082_1107_, 1);
lean_inc(v_v_1129_);
v_p_1130_ = lean_ctor_get(v_p_u2082_1107_, 2);
lean_inc_ref(v_p_1130_);
lean_dec_ref_known(v_p_u2082_1107_, 3);
v___x_1131_ = lean_apply_6(v_h__4_1111_, v_k_1125_, v_v_1126_, v_p_1127_, v_k_1128_, v_v_1129_, v_p_1130_);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_not__le__of__le__cert(lean_object* v_p_u2081_1132_, lean_object* v_p_u2082_1133_){
_start:
{
if (lean_obj_tag(v_p_u2081_1132_) == 0)
{
if (lean_obj_tag(v_p_u2082_1133_) == 0)
{
lean_object* v_k_1134_; lean_object* v_k_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_k_1134_ = lean_ctor_get(v_p_u2081_1132_, 0);
v_k_1135_ = lean_ctor_get(v_p_u2082_1133_, 0);
v___x_1136_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_1137_ = lean_int_sub(v___x_1136_, v_k_1135_);
v___x_1138_ = lean_int_dec_le(v___x_1137_, v_k_1134_);
lean_dec(v___x_1137_);
return v___x_1138_;
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = 0;
return v___x_1139_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1133_) == 0)
{
uint8_t v___x_1140_; 
v___x_1140_ = 0;
return v___x_1140_;
}
else
{
lean_object* v_k_1141_; lean_object* v_v_1142_; lean_object* v_p_1143_; lean_object* v_k_1144_; lean_object* v_v_1145_; lean_object* v_p_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_k_1141_ = lean_ctor_get(v_p_u2081_1132_, 0);
v_v_1142_ = lean_ctor_get(v_p_u2081_1132_, 1);
v_p_1143_ = lean_ctor_get(v_p_u2081_1132_, 2);
v_k_1144_ = lean_ctor_get(v_p_u2082_1133_, 0);
v_v_1145_ = lean_ctor_get(v_p_u2082_1133_, 1);
v_p_1146_ = lean_ctor_get(v_p_u2082_1133_, 2);
v___x_1147_ = lean_int_neg(v_k_1144_);
v___x_1148_ = lean_int_dec_eq(v_k_1141_, v___x_1147_);
lean_dec(v___x_1147_);
if (v___x_1148_ == 0)
{
return v___x_1148_;
}
else
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_nat_dec_eq(v_v_1142_, v_v_1145_);
if (v___x_1149_ == 0)
{
return v___x_1149_;
}
else
{
v_p_u2081_1132_ = v_p_1143_;
v_p_u2082_1133_ = v_p_1146_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_not__le__of__le__cert___boxed(lean_object* v_p_u2081_1151_, lean_object* v_p_u2082_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l_Int_Internal_Linear_not__le__of__le__cert(v_p_u2081_1151_, v_p_u2082_1152_);
lean_dec_ref(v_p_u2082_1152_);
lean_dec_ref(v_p_u2081_1151_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Cooper(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Linear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Cooper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_Internal_Linear_instInhabitedExpr_default = _init_l_Int_Internal_Linear_instInhabitedExpr_default();
lean_mark_persistent(l_Int_Internal_Linear_instInhabitedExpr_default);
l_Int_Internal_Linear_instInhabitedExpr = _init_l_Int_Internal_Linear_instInhabitedExpr();
lean_mark_persistent(l_Int_Internal_Linear_instInhabitedExpr);
l_Int_Internal_Linear_hugeFuel = _init_l_Int_Internal_Linear_hugeFuel();
lean_mark_persistent(l_Int_Internal_Linear_hugeFuel);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Linear(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Cooper(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Cooper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Linear(builtin);
}
#ifdef __cplusplus
}
#endif
