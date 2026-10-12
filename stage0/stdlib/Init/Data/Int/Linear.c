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
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDvd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff___boxed(lean_object*, lean_object*);
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
uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object* v_x_103_, lean_object* v_x_104_){
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
LEAN_EXPORT void l_Int_Internal_Linear_instBEqExpr_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_103_ = stack[0].m_obj;
lean_object* v_x_104_ = stack[1].m_obj;
uint8_t v_res_148_;
v_res_148_ = l_Int_Internal_Linear_instBEqExpr_beq(v_x_103_, v_x_104_);
stack->m_num = v_res_148_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instBEqExpr_beq___boxed(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Int_Internal_Linear_instBEqExpr_beq(v_x_149_, v_x_150_);
lean_dec_ref(v_x_150_);
lean_dec_ref(v_x_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denote(lean_object* v_ctx_155_, lean_object* v_x_156_){
_start:
{
switch(lean_obj_tag(v_x_156_))
{
case 0:
{
lean_object* v_v_157_; 
v_v_157_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_v_157_);
return v_v_157_;
}
case 1:
{
lean_object* v_i_158_; lean_object* v___x_159_; 
v_i_158_ = lean_ctor_get(v_x_156_, 0);
v___x_159_ = l_Lean_RArray_getImpl___redArg(v_ctx_155_, v_i_158_);
return v___x_159_;
}
case 2:
{
lean_object* v_a_160_; lean_object* v_b_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_a_160_ = lean_ctor_get(v_x_156_, 0);
v_b_161_ = lean_ctor_get(v_x_156_, 1);
v___x_162_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_a_160_);
v___x_163_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_b_161_);
v___x_164_ = lean_int_add(v___x_162_, v___x_163_);
lean_dec(v___x_163_);
lean_dec(v___x_162_);
return v___x_164_;
}
case 3:
{
lean_object* v_a_165_; lean_object* v_b_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_165_ = lean_ctor_get(v_x_156_, 0);
v_b_166_ = lean_ctor_get(v_x_156_, 1);
v___x_167_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_a_165_);
v___x_168_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_b_166_);
v___x_169_ = lean_int_sub(v___x_167_, v___x_168_);
lean_dec(v___x_168_);
lean_dec(v___x_167_);
return v___x_169_;
}
case 4:
{
lean_object* v_a_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_a_170_ = lean_ctor_get(v_x_156_, 0);
v___x_171_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_a_170_);
v___x_172_ = lean_int_neg(v___x_171_);
lean_dec(v___x_171_);
return v___x_172_;
}
case 5:
{
lean_object* v_k_173_; lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_k_173_ = lean_ctor_get(v_x_156_, 0);
v_a_174_ = lean_ctor_get(v_x_156_, 1);
v___x_175_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_a_174_);
v___x_176_ = lean_int_mul(v_k_173_, v___x_175_);
lean_dec(v___x_175_);
return v___x_176_;
}
default: 
{
lean_object* v_a_177_; lean_object* v_k_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_a_177_ = lean_ctor_get(v_x_156_, 0);
v_k_178_ = lean_ctor_get(v_x_156_, 1);
v___x_179_ = l_Int_Internal_Linear_Expr_denote(v_ctx_155_, v_a_177_);
v___x_180_ = lean_int_mul(v___x_179_, v_k_178_);
lean_dec(v___x_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denote___boxed(lean_object* v_ctx_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Int_Internal_Linear_Expr_denote(v_ctx_181_, v_x_182_);
lean_dec_ref(v_x_182_);
lean_dec_ref(v_ctx_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorIdx___impl(lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_tag_nat(v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorIdx___impl___boxed(lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Int_Internal_Linear_Poly_ctorIdx___impl(v_x_186_);
lean_dec_ref(v_x_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim___redArg(lean_object* v_t_188_, lean_object* v_k_189_){
_start:
{
if (lean_obj_tag(v_t_188_) == 0)
{
lean_object* v_k_190_; lean_object* v___x_191_; 
v_k_190_ = lean_ctor_get(v_t_188_, 0);
lean_inc(v_k_190_);
lean_dec_ref_known(v_t_188_, 1);
v___x_191_ = lean_apply_1(v_k_189_, v_k_190_);
return v___x_191_;
}
else
{
lean_object* v_k_192_; lean_object* v_v_193_; lean_object* v_p_194_; lean_object* v___x_195_; 
v_k_192_ = lean_ctor_get(v_t_188_, 0);
lean_inc(v_k_192_);
v_v_193_ = lean_ctor_get(v_t_188_, 1);
lean_inc(v_v_193_);
v_p_194_ = lean_ctor_get(v_t_188_, 2);
lean_inc_ref(v_p_194_);
lean_dec_ref_known(v_t_188_, 3);
v___x_195_ = lean_apply_3(v_k_189_, v_k_192_, v_v_193_, v_p_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim(lean_object* v_motive_196_, lean_object* v_ctorIdx_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_k_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_198_, v_k_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_ctorElim___boxed(lean_object* v_motive_202_, lean_object* v_ctorIdx_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_k_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Int_Internal_Linear_Poly_ctorElim(v_motive_202_, v_ctorIdx_203_, v_t_204_, v_h_205_, v_k_206_);
lean_dec(v_ctorIdx_203_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_num_elim___redArg(lean_object* v_t_208_, lean_object* v_num_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_208_, v_num_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_num_elim(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_num_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_212_, v_num_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_add_elim___redArg(lean_object* v_t_216_, lean_object* v_add_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_216_, v_add_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_add_elim(lean_object* v_motive_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_add_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Int_Internal_Linear_Poly_ctorElim___redArg(v_t_220_, v_add_222_);
return v___x_223_;
}
}
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v_k_226_; lean_object* v_k_227_; uint8_t v___x_228_; 
v_k_226_ = lean_ctor_get(v_x_224_, 0);
v_k_227_ = lean_ctor_get(v_x_225_, 0);
v___x_228_ = lean_int_dec_eq(v_k_226_, v_k_227_);
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
else
{
if (lean_obj_tag(v_x_225_) == 1)
{
lean_object* v_k_230_; lean_object* v_v_231_; lean_object* v_p_232_; lean_object* v_k_233_; lean_object* v_v_234_; lean_object* v_p_235_; uint8_t v___x_236_; 
v_k_230_ = lean_ctor_get(v_x_224_, 0);
v_v_231_ = lean_ctor_get(v_x_224_, 1);
v_p_232_ = lean_ctor_get(v_x_224_, 2);
v_k_233_ = lean_ctor_get(v_x_225_, 0);
v_v_234_ = lean_ctor_get(v_x_225_, 1);
v_p_235_ = lean_ctor_get(v_x_225_, 2);
v___x_236_ = lean_int_dec_eq(v_k_230_, v_k_233_);
if (v___x_236_ == 0)
{
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = lean_nat_dec_eq(v_v_231_, v_v_234_);
if (v___x_237_ == 0)
{
return v___x_237_;
}
else
{
v_x_224_ = v_p_232_;
v_x_225_ = v_p_235_;
goto _start;
}
}
}
else
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_instBEqPoly_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_224_ = stack[0].m_obj;
lean_object* v_x_225_ = stack[1].m_obj;
uint8_t v_res_240_;
v_res_240_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_224_, v_x_225_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instBEqPoly_beq___boxed(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_241_, v_x_242_);
lean_dec_ref(v_x_242_);
lean_dec_ref(v_x_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_, lean_object* v_h__3_251_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_dec(v_h__2_250_);
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v_k_252_; lean_object* v_k_253_; lean_object* v___x_254_; 
lean_dec(v_h__3_251_);
v_k_252_ = lean_ctor_get(v_x_247_, 0);
lean_inc(v_k_252_);
lean_dec_ref_known(v_x_247_, 1);
v_k_253_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_k_253_);
lean_dec_ref_known(v_x_248_, 1);
v___x_254_ = lean_apply_2(v_h__1_249_, v_k_252_, v_k_253_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
lean_dec(v_h__1_249_);
v___x_255_ = lean_apply_4(v_h__3_251_, v_x_247_, v_x_248_, lean_box(0), lean_box(0));
return v___x_255_;
}
}
else
{
lean_dec(v_h__1_249_);
if (lean_obj_tag(v_x_248_) == 1)
{
lean_object* v_k_256_; lean_object* v_v_257_; lean_object* v_p_258_; lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_p_261_; lean_object* v___x_262_; 
lean_dec(v_h__3_251_);
v_k_256_ = lean_ctor_get(v_x_247_, 0);
lean_inc(v_k_256_);
v_v_257_ = lean_ctor_get(v_x_247_, 1);
lean_inc(v_v_257_);
v_p_258_ = lean_ctor_get(v_x_247_, 2);
lean_inc_ref(v_p_258_);
lean_dec_ref_known(v_x_247_, 3);
v_k_259_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_k_259_);
v_v_260_ = lean_ctor_get(v_x_248_, 1);
lean_inc(v_v_260_);
v_p_261_ = lean_ctor_get(v_x_248_, 2);
lean_inc_ref(v_p_261_);
lean_dec_ref_known(v_x_248_, 3);
v___x_262_ = lean_apply_6(v_h__2_250_, v_k_256_, v_v_257_, v_p_258_, v_k_259_, v_v_260_, v_p_261_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
lean_dec(v_h__2_250_);
v___x_263_ = lean_apply_4(v_h__3_251_, v_x_247_, v_x_248_, lean_box(0), lean_box(0));
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_, lean_object* v_h__3_269_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_dec(v_h__2_268_);
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v_k_270_; lean_object* v_k_271_; lean_object* v___x_272_; 
lean_dec(v_h__3_269_);
v_k_270_ = lean_ctor_get(v_x_265_, 0);
lean_inc(v_k_270_);
lean_dec_ref_known(v_x_265_, 1);
v_k_271_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_k_271_);
lean_dec_ref_known(v_x_266_, 1);
v___x_272_ = lean_apply_2(v_h__1_267_, v_k_270_, v_k_271_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; 
lean_dec(v_h__1_267_);
v___x_273_ = lean_apply_4(v_h__3_269_, v_x_265_, v_x_266_, lean_box(0), lean_box(0));
return v___x_273_;
}
}
else
{
lean_dec(v_h__1_267_);
if (lean_obj_tag(v_x_266_) == 1)
{
lean_object* v_k_274_; lean_object* v_v_275_; lean_object* v_p_276_; lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v_p_279_; lean_object* v___x_280_; 
lean_dec(v_h__3_269_);
v_k_274_ = lean_ctor_get(v_x_265_, 0);
lean_inc(v_k_274_);
v_v_275_ = lean_ctor_get(v_x_265_, 1);
lean_inc(v_v_275_);
v_p_276_ = lean_ctor_get(v_x_265_, 2);
lean_inc_ref(v_p_276_);
lean_dec_ref_known(v_x_265_, 3);
v_k_277_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_k_277_);
v_v_278_ = lean_ctor_get(v_x_266_, 1);
lean_inc(v_v_278_);
v_p_279_ = lean_ctor_get(v_x_266_, 2);
lean_inc_ref(v_p_279_);
lean_dec_ref_known(v_x_266_, 3);
v___x_280_ = lean_apply_6(v_h__2_268_, v_k_274_, v_v_275_, v_p_276_, v_k_277_, v_v_278_, v_p_279_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; 
lean_dec(v_h__2_268_);
v___x_281_ = lean_apply_4(v_h__3_269_, v_x_265_, v_x_266_, lean_box(0), lean_box(0));
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denote(lean_object* v_ctx_282_, lean_object* v_p_283_){
_start:
{
if (lean_obj_tag(v_p_283_) == 0)
{
lean_object* v_k_284_; 
v_k_284_ = lean_ctor_get(v_p_283_, 0);
lean_inc(v_k_284_);
return v_k_284_;
}
else
{
lean_object* v_k_285_; lean_object* v_v_286_; lean_object* v_p_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_k_285_ = lean_ctor_get(v_p_283_, 0);
v_v_286_ = lean_ctor_get(v_p_283_, 1);
v_p_287_ = lean_ctor_get(v_p_283_, 2);
v___x_288_ = l_Lean_RArray_getImpl___redArg(v_ctx_282_, v_v_286_);
v___x_289_ = lean_int_mul(v_k_285_, v___x_288_);
lean_dec(v___x_288_);
v___x_290_ = l_Int_Internal_Linear_Poly_denote(v_ctx_282_, v_p_287_);
v___x_291_ = lean_int_add(v___x_289_, v___x_290_);
lean_dec(v___x_290_);
lean_dec(v___x_289_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denote___boxed(lean_object* v_ctx_292_, lean_object* v_p_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Int_Internal_Linear_Poly_denote(v_ctx_292_, v_p_293_);
lean_dec_ref(v_p_293_);
lean_dec_ref(v_ctx_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_denote_match__1_splitter___redArg(lean_object* v_p_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
if (lean_obj_tag(v_p_295_) == 0)
{
lean_object* v_k_298_; lean_object* v___x_299_; 
lean_dec(v_h__2_297_);
v_k_298_ = lean_ctor_get(v_p_295_, 0);
lean_inc(v_k_298_);
lean_dec_ref_known(v_p_295_, 1);
v___x_299_ = lean_apply_1(v_h__1_296_, v_k_298_);
return v___x_299_;
}
else
{
lean_object* v_k_300_; lean_object* v_v_301_; lean_object* v_p_302_; lean_object* v___x_303_; 
lean_dec(v_h__1_296_);
v_k_300_ = lean_ctor_get(v_p_295_, 0);
lean_inc(v_k_300_);
v_v_301_ = lean_ctor_get(v_p_295_, 1);
lean_inc(v_v_301_);
v_p_302_ = lean_ctor_get(v_p_295_, 2);
lean_inc_ref(v_p_302_);
lean_dec_ref_known(v_p_295_, 3);
v___x_303_ = lean_apply_3(v_h__2_297_, v_k_300_, v_v_301_, v_p_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_denote_match__1_splitter(lean_object* v_motive_304_, lean_object* v_p_305_, lean_object* v_h__1_306_, lean_object* v_h__2_307_){
_start:
{
if (lean_obj_tag(v_p_305_) == 0)
{
lean_object* v_k_308_; lean_object* v___x_309_; 
lean_dec(v_h__2_307_);
v_k_308_ = lean_ctor_get(v_p_305_, 0);
lean_inc(v_k_308_);
lean_dec_ref_known(v_p_305_, 1);
v___x_309_ = lean_apply_1(v_h__1_306_, v_k_308_);
return v___x_309_;
}
else
{
lean_object* v_k_310_; lean_object* v_v_311_; lean_object* v_p_312_; lean_object* v___x_313_; 
lean_dec(v_h__1_306_);
v_k_310_ = lean_ctor_get(v_p_305_, 0);
lean_inc(v_k_310_);
v_v_311_ = lean_ctor_get(v_p_305_, 1);
lean_inc(v_v_311_);
v_p_312_ = lean_ctor_get(v_p_305_, 2);
lean_inc_ref(v_p_312_);
lean_dec_ref_known(v_p_305_, 3);
v___x_313_ = lean_apply_3(v_h__2_307_, v_k_310_, v_v_311_, v_p_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object* v_p_314_, lean_object* v_k_315_){
_start:
{
if (lean_obj_tag(v_p_314_) == 0)
{
lean_object* v_k_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_k_316_ = lean_ctor_get(v_p_314_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_p_314_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v_p_314_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_k_316_);
lean_dec(v_p_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_int_add(v_k_315_, v_k_316_);
lean_dec(v_k_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_p_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_k_325_ = lean_ctor_get(v_p_314_, 0);
v_v_326_ = lean_ctor_get(v_p_314_, 1);
v_p_327_ = lean_ctor_get(v_p_314_, 2);
v_isSharedCheck_335_ = !lean_is_exclusive(v_p_314_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v_p_314_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_p_327_);
lean_inc(v_v_326_);
lean_inc(v_k_325_);
lean_dec(v_p_314_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = l_Int_Internal_Linear_Poly_addConst(v_p_327_, v_k_315_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 2, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_k_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_v_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_addConst___boxed(lean_object* v_p_336_, lean_object* v_k_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Int_Internal_Linear_Poly_addConst(v_p_336_, v_k_337_);
lean_dec(v_k_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_insert(lean_object* v_k_339_, lean_object* v_v_340_, lean_object* v_p_341_){
_start:
{
if (lean_obj_tag(v_p_341_) == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v_k_339_);
lean_ctor_set(v___x_342_, 1, v_v_340_);
lean_ctor_set(v___x_342_, 2, v_p_341_);
return v___x_342_;
}
else
{
lean_object* v_k_343_; lean_object* v_v_344_; lean_object* v_p_345_; uint8_t v___x_346_; 
v_k_343_ = lean_ctor_get(v_p_341_, 0);
v_v_344_ = lean_ctor_get(v_p_341_, 1);
v_p_345_ = lean_ctor_get(v_p_341_, 2);
v___x_346_ = l_Nat_blt(v_v_344_, v_v_340_);
if (v___x_346_ == 0)
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_361_; 
lean_inc_ref(v_p_345_);
lean_inc(v_v_344_);
lean_inc(v_k_343_);
v_isSharedCheck_361_ = !lean_is_exclusive(v_p_341_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_362_ = lean_ctor_get(v_p_341_, 2);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_p_341_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_p_341_, 0);
lean_dec(v_unused_364_);
v___x_348_ = v_p_341_;
v_isShared_349_ = v_isSharedCheck_361_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_p_341_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_361_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint8_t v___x_350_; 
v___x_350_ = lean_nat_dec_eq(v_v_340_, v_v_344_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = l_Int_Internal_Linear_Poly_insert(v_k_339_, v_v_340_, v_p_345_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 2, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_k_343_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
lean_dec(v_v_340_);
v___x_355_ = lean_int_add(v_k_339_, v_k_343_);
lean_dec(v_k_343_);
lean_dec(v_k_339_);
v___x_356_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_357_ = lean_int_dec_eq(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_359_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_355_);
v___x_359_ = v___x_348_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_p_345_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_dec(v___x_355_);
lean_del_object(v___x_348_);
lean_dec(v_v_344_);
return v_p_345_;
}
}
}
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_365_, 0, v_k_339_);
lean_ctor_set(v___x_365_, 1, v_v_340_);
lean_ctor_set(v___x_365_, 2, v_p_341_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_norm(lean_object* v_p_366_){
_start:
{
if (lean_obj_tag(v_p_366_) == 0)
{
return v_p_366_;
}
else
{
lean_object* v_k_367_; lean_object* v_v_368_; lean_object* v_p_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_k_367_ = lean_ctor_get(v_p_366_, 0);
lean_inc(v_k_367_);
v_v_368_ = lean_ctor_get(v_p_366_, 1);
lean_inc(v_v_368_);
v_p_369_ = lean_ctor_get(v_p_366_, 2);
lean_inc_ref(v_p_369_);
lean_dec_ref_known(v_p_366_, 3);
v___x_370_ = l_Int_Internal_Linear_Poly_norm(v_p_369_);
v___x_371_ = l_Int_Internal_Linear_Poly_insert(v_k_367_, v_v_368_, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_append(lean_object* v_p_u2081_372_, lean_object* v_p_u2082_373_){
_start:
{
if (lean_obj_tag(v_p_u2081_372_) == 0)
{
lean_object* v_k_374_; lean_object* v___x_375_; 
v_k_374_ = lean_ctor_get(v_p_u2081_372_, 0);
lean_inc(v_k_374_);
lean_dec_ref_known(v_p_u2081_372_, 1);
v___x_375_ = l_Int_Internal_Linear_Poly_addConst(v_p_u2082_373_, v_k_374_);
lean_dec(v_k_374_);
return v___x_375_;
}
else
{
lean_object* v_k_376_; lean_object* v_v_377_; lean_object* v_p_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_k_376_ = lean_ctor_get(v_p_u2081_372_, 0);
v_v_377_ = lean_ctor_get(v_p_u2081_372_, 1);
v_p_378_ = lean_ctor_get(v_p_u2081_372_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_p_u2081_372_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v_p_u2081_372_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_p_378_);
lean_inc(v_v_377_);
lean_inc(v_k_376_);
lean_dec(v_p_u2081_372_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = l_Int_Internal_Linear_Poly_append(v_p_378_, v_p_u2082_373_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_k_376_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_v_377_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_combine_x27(lean_object* v_fuel_387_, lean_object* v_p_u2081_388_, lean_object* v_p_u2082_389_){
_start:
{
lean_object* v_zero_390_; uint8_t v_isZero_391_; 
v_zero_390_ = lean_unsigned_to_nat(0u);
v_isZero_391_ = lean_nat_dec_eq(v_fuel_387_, v_zero_390_);
if (v_isZero_391_ == 1)
{
lean_object* v___x_392_; 
lean_dec(v_fuel_387_);
v___x_392_ = l_Int_Internal_Linear_Poly_append(v_p_u2081_388_, v_p_u2082_389_);
return v___x_392_;
}
else
{
lean_object* v_one_393_; lean_object* v_n_394_; 
v_one_393_ = lean_unsigned_to_nat(1u);
v_n_394_ = lean_nat_sub(v_fuel_387_, v_one_393_);
lean_dec(v_fuel_387_);
if (lean_obj_tag(v_p_u2081_388_) == 0)
{
if (lean_obj_tag(v_p_u2082_389_) == 0)
{
lean_object* v_k_395_; lean_object* v_k_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_n_394_);
v_k_395_ = lean_ctor_get(v_p_u2081_388_, 0);
lean_inc(v_k_395_);
lean_dec_ref_known(v_p_u2081_388_, 1);
v_k_396_ = lean_ctor_get(v_p_u2082_389_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_p_u2082_389_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v_p_u2082_389_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_k_396_);
lean_dec(v_p_u2082_389_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_int_add(v_k_395_, v_k_396_);
lean_dec(v_k_396_);
lean_dec(v_k_395_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_k_405_; lean_object* v_v_406_; lean_object* v_p_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_k_405_ = lean_ctor_get(v_p_u2082_389_, 0);
v_v_406_ = lean_ctor_get(v_p_u2082_389_, 1);
v_p_407_ = lean_ctor_get(v_p_u2082_389_, 2);
v_isSharedCheck_415_ = !lean_is_exclusive(v_p_u2082_389_);
if (v_isSharedCheck_415_ == 0)
{
v___x_409_ = v_p_u2082_389_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_p_407_);
lean_inc(v_v_406_);
lean_inc(v_k_405_);
lean_dec(v_p_u2082_389_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_394_, v_p_u2081_388_, v_p_407_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 2, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_k_405_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_v_406_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
if (lean_obj_tag(v_p_u2082_389_) == 0)
{
lean_object* v_k_416_; lean_object* v_v_417_; lean_object* v_p_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_k_416_ = lean_ctor_get(v_p_u2081_388_, 0);
v_v_417_ = lean_ctor_get(v_p_u2081_388_, 1);
v_p_418_ = lean_ctor_get(v_p_u2081_388_, 2);
v_isSharedCheck_426_ = !lean_is_exclusive(v_p_u2081_388_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v_p_u2081_388_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_p_418_);
lean_inc(v_v_417_);
lean_inc(v_k_416_);
lean_dec(v_p_u2081_388_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_394_, v_p_418_, v_p_u2082_389_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 2, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_k_416_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_v_417_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_k_427_; lean_object* v_v_428_; lean_object* v_p_429_; lean_object* v_k_430_; lean_object* v_v_431_; lean_object* v_p_432_; uint8_t v___x_433_; 
v_k_427_ = lean_ctor_get(v_p_u2081_388_, 0);
v_v_428_ = lean_ctor_get(v_p_u2081_388_, 1);
v_p_429_ = lean_ctor_get(v_p_u2081_388_, 2);
v_k_430_ = lean_ctor_get(v_p_u2082_389_, 0);
v_v_431_ = lean_ctor_get(v_p_u2082_389_, 1);
v_p_432_ = lean_ctor_get(v_p_u2082_389_, 2);
v___x_433_ = lean_nat_dec_eq(v_v_428_, v_v_431_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = l_Nat_blt(v_v_431_, v_v_428_);
if (v___x_434_ == 0)
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
lean_inc_ref(v_p_432_);
lean_inc(v_v_431_);
lean_inc(v_k_430_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_p_u2082_389_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_443_ = lean_ctor_get(v_p_u2082_389_, 2);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_p_u2082_389_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_p_u2082_389_, 0);
lean_dec(v_unused_445_);
v___x_436_ = v_p_u2082_389_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_dec(v_p_u2082_389_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_394_, v_p_u2081_388_, v_p_432_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 2, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_k_430_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_v_431_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
lean_inc_ref(v_p_429_);
lean_inc(v_v_428_);
lean_inc(v_k_427_);
v_isSharedCheck_453_ = !lean_is_exclusive(v_p_u2081_388_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; 
v_unused_454_ = lean_ctor_get(v_p_u2081_388_, 2);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_p_u2081_388_, 1);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_p_u2081_388_, 0);
lean_dec(v_unused_456_);
v___x_447_ = v_p_u2081_388_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_p_u2081_388_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_394_, v_p_429_, v_p_u2082_389_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_k_427_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_v_428_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v___x_449_);
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
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_468_; 
lean_inc_ref(v_p_432_);
lean_inc(v_k_430_);
lean_inc_ref(v_p_429_);
lean_inc(v_v_428_);
lean_inc(v_k_427_);
lean_dec_ref_known(v_p_u2081_388_, 3);
v_isSharedCheck_468_ = !lean_is_exclusive(v_p_u2082_389_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_469_ = lean_ctor_get(v_p_u2082_389_, 2);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_p_u2082_389_, 1);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_p_u2082_389_, 0);
lean_dec(v_unused_471_);
v___x_458_ = v_p_u2082_389_;
v_isShared_459_ = v_isSharedCheck_468_;
goto v_resetjp_457_;
}
else
{
lean_dec(v_p_u2082_389_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_468_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_a_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_a_460_ = lean_int_add(v_k_427_, v_k_430_);
lean_dec(v_k_430_);
lean_dec(v_k_427_);
v___x_461_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_462_ = lean_int_dec_eq(v_a_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = l_Int_Internal_Linear_Poly_combine_x27(v_n_394_, v_p_429_, v_p_432_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 2, v___x_463_);
lean_ctor_set(v___x_458_, 1, v_v_428_);
lean_ctor_set(v___x_458_, 0, v_a_460_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_v_428_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_dec(v_a_460_);
lean_del_object(v___x_458_);
lean_dec(v_v_428_);
v_fuel_387_ = v_n_394_;
v_p_u2081_388_ = v_p_429_;
v_p_u2082_389_ = v_p_432_;
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
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(100000000u);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_combine(lean_object* v_p_u2081_473_, lean_object* v_p_u2082_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(100000000u);
v___x_476_ = l_Int_Internal_Linear_Poly_combine_x27(v___x_475_, v_p_u2081_473_, v_p_u2082_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27_go(lean_object* v_coeff_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
switch(lean_obj_tag(v_a_478_))
{
case 0:
{
lean_object* v_v_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_v_480_ = lean_ctor_get(v_a_478_, 0);
v___x_481_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_482_ = lean_int_dec_eq(v_v_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_int_mul(v_coeff_477_, v_v_480_);
lean_dec(v_coeff_477_);
v___x_484_ = l_Int_Internal_Linear_Poly_addConst(v_a_479_, v___x_483_);
lean_dec(v___x_483_);
return v___x_484_;
}
else
{
lean_dec(v_coeff_477_);
return v_a_479_;
}
}
case 1:
{
lean_object* v_i_485_; lean_object* v___x_486_; 
v_i_485_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_i_485_);
v___x_486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_486_, 0, v_coeff_477_);
lean_ctor_set(v___x_486_, 1, v_i_485_);
lean_ctor_set(v___x_486_, 2, v_a_479_);
return v___x_486_;
}
case 2:
{
lean_object* v_a_487_; lean_object* v_b_488_; lean_object* v___x_489_; 
v_a_487_ = lean_ctor_get(v_a_478_, 0);
v_b_488_ = lean_ctor_get(v_a_478_, 1);
lean_inc(v_coeff_477_);
v___x_489_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v_coeff_477_, v_b_488_, v_a_479_);
v_a_478_ = v_a_487_;
v_a_479_ = v___x_489_;
goto _start;
}
case 3:
{
lean_object* v_a_491_; lean_object* v_b_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_491_ = lean_ctor_get(v_a_478_, 0);
v_b_492_ = lean_ctor_get(v_a_478_, 1);
v___x_493_ = lean_int_neg(v_coeff_477_);
v___x_494_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v___x_493_, v_b_492_, v_a_479_);
v_a_478_ = v_a_491_;
v_a_479_ = v___x_494_;
goto _start;
}
case 4:
{
lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_496_ = lean_ctor_get(v_a_478_, 0);
v___x_497_ = lean_int_neg(v_coeff_477_);
lean_dec(v_coeff_477_);
v_coeff_477_ = v___x_497_;
v_a_478_ = v_a_496_;
goto _start;
}
case 5:
{
lean_object* v_k_499_; lean_object* v_a_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_k_499_ = lean_ctor_get(v_a_478_, 0);
v_a_500_ = lean_ctor_get(v_a_478_, 1);
v___x_501_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_502_ = lean_int_dec_eq(v_k_499_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_int_mul(v_coeff_477_, v_k_499_);
lean_dec(v_coeff_477_);
v_coeff_477_ = v___x_503_;
v_a_478_ = v_a_500_;
goto _start;
}
else
{
lean_dec(v_coeff_477_);
return v_a_479_;
}
}
default: 
{
lean_object* v_a_505_; lean_object* v_k_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_a_505_ = lean_ctor_get(v_a_478_, 0);
v_k_506_ = lean_ctor_get(v_a_478_, 1);
v___x_507_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_508_ = lean_int_dec_eq(v_k_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_int_mul(v_coeff_477_, v_k_506_);
lean_dec(v_coeff_477_);
v_coeff_477_ = v___x_509_;
v_a_478_ = v_a_505_;
goto _start;
}
else
{
lean_dec(v_coeff_477_);
return v_a_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27_go___boxed(lean_object* v_coeff_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v_coeff_511_, v_a_512_, v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_514_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27(lean_object* v_e_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_521_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__1, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1);
v___x_522_ = l_Int_Internal_Linear_Expr_toPoly_x27_go(v___x_520_, v_e_519_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_toPoly_x27___boxed(lean_object* v_e_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Int_Internal_Linear_Expr_toPoly_x27(v_e_523_);
lean_dec_ref(v_e_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_norm(lean_object* v_e_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l_Int_Internal_Linear_Expr_toPoly_x27(v_e_525_);
v___x_527_ = l_Int_Internal_Linear_Poly_norm(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_norm___boxed(lean_object* v_e_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Int_Internal_Linear_Expr_norm(v_e_528_);
lean_dec_ref(v_e_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cdiv(lean_object* v_a_530_, lean_object* v_b_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_int_neg(v_a_530_);
v___x_533_ = lean_int_ediv(v___x_532_, v_b_531_);
lean_dec(v___x_532_);
v___x_534_ = lean_int_neg(v___x_533_);
lean_dec(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cdiv___boxed(lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Int_Internal_Linear_cdiv(v_a_535_, v_b_536_);
lean_dec(v_b_536_);
lean_dec(v_a_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cmod(lean_object* v_a_538_, lean_object* v_b_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_int_neg(v_a_538_);
v___x_541_ = lean_int_emod(v___x_540_, v_b_539_);
lean_dec(v___x_540_);
v___x_542_ = lean_int_neg(v___x_541_);
lean_dec(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_cmod___boxed(lean_object* v_a_543_, lean_object* v_b_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Int_Internal_Linear_cmod(v_a_543_, v_b_544_);
lean_dec(v_b_544_);
lean_dec(v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_object* v_k_547_; 
v_k_547_ = lean_ctor_get(v_x_546_, 0);
lean_inc(v_k_547_);
return v_k_547_;
}
else
{
lean_object* v_p_548_; 
v_p_548_ = lean_ctor_get(v_x_546_, 2);
v_x_546_ = v_p_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_getConst___boxed(lean_object* v_x_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Int_Internal_Linear_Poly_getConst(v_x_550_);
lean_dec_ref(v_x_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_div(lean_object* v_k_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v_k_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_k_554_ = lean_ctor_get(v_x_553_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v_x_553_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_k_554_);
lean_dec(v_x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = l_Int_Internal_Linear_cdiv(v_k_554_, v_k_552_);
lean_dec(v_k_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_k_563_; lean_object* v_v_564_; lean_object* v_p_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
v_k_563_ = lean_ctor_get(v_x_553_, 0);
v_v_564_ = lean_ctor_get(v_x_553_, 1);
v_p_565_ = lean_ctor_get(v_x_553_, 2);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_574_ == 0)
{
v___x_567_ = v_x_553_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_p_565_);
lean_inc(v_v_564_);
lean_inc(v_k_563_);
lean_dec(v_x_553_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_int_ediv(v_k_563_, v_k_552_);
lean_dec(v_k_563_);
v___x_570_ = l_Int_Internal_Linear_Poly_div(v_k_552_, v_p_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 2, v___x_570_);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_div___boxed(lean_object* v_k_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Int_Internal_Linear_Poly_div(v_k_575_, v_x_576_);
lean_dec(v_k_575_);
return v_res_577_;
}
}
uint8_t l_Int_Internal_Linear_Poly_divAll(lean_object* v_k_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_k_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_k_580_ = lean_ctor_get(v_x_579_, 0);
v___x_581_ = lean_int_emod(v_k_580_, v_k_578_);
v___x_582_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_583_ = lean_int_dec_eq(v___x_581_, v___x_582_);
lean_dec(v___x_581_);
return v___x_583_;
}
else
{
lean_object* v_k_584_; lean_object* v_p_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_k_584_ = lean_ctor_get(v_x_579_, 0);
v_p_585_ = lean_ctor_get(v_x_579_, 2);
v___x_586_ = lean_int_emod(v_k_584_, v_k_578_);
v___x_587_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_588_ = lean_int_dec_eq(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
if (v___x_588_ == 0)
{
return v___x_588_;
}
else
{
v_x_579_ = v_p_585_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_divAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_578_ = stack[0].m_obj;
lean_object* v_x_579_ = stack[1].m_obj;
uint8_t v_res_590_;
v_res_590_ = l_Int_Internal_Linear_Poly_divAll(v_k_578_, v_x_579_);
stack->m_num = v_res_590_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divAll___boxed(lean_object* v_k_591_, lean_object* v_x_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Int_Internal_Linear_Poly_divAll(v_k_591_, v_x_592_);
lean_dec_ref(v_x_592_);
lean_dec(v_k_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
uint8_t l_Int_Internal_Linear_Poly_divCoeffs(lean_object* v_k_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
uint8_t v___x_597_; 
v___x_597_ = 1;
return v___x_597_;
}
else
{
lean_object* v_k_598_; lean_object* v_p_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_k_598_ = lean_ctor_get(v_x_596_, 0);
v_p_599_ = lean_ctor_get(v_x_596_, 2);
v___x_600_ = lean_int_emod(v_k_598_, v_k_595_);
v___x_601_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_602_ = lean_int_dec_eq(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
if (v___x_602_ == 0)
{
return v___x_602_;
}
else
{
v_x_596_ = v_p_599_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_divCoeffs_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_595_ = stack[0].m_obj;
lean_object* v_x_596_ = stack[1].m_obj;
uint8_t v_res_604_;
v_res_604_ = l_Int_Internal_Linear_Poly_divCoeffs(v_k_595_, v_x_596_);
stack->m_num = v_res_604_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divCoeffs___boxed(lean_object* v_k_605_, lean_object* v_x_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Int_Internal_Linear_Poly_divCoeffs(v_k_605_, v_x_606_);
lean_dec_ref(v_x_606_);
lean_dec(v_k_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27(lean_object* v_p_609_, lean_object* v_k_610_){
_start:
{
if (lean_obj_tag(v_p_609_) == 0)
{
lean_object* v_k_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_k_611_ = lean_ctor_get(v_p_609_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_p_609_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v_p_609_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_k_611_);
lean_dec(v_p_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_int_mul(v_k_610_, v_k_611_);
lean_dec(v_k_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
lean_object* v_k_620_; lean_object* v_v_621_; lean_object* v_p_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_631_; 
v_k_620_ = lean_ctor_get(v_p_609_, 0);
v_v_621_ = lean_ctor_get(v_p_609_, 1);
v_p_622_ = lean_ctor_get(v_p_609_, 2);
v_isSharedCheck_631_ = !lean_is_exclusive(v_p_609_);
if (v_isSharedCheck_631_ == 0)
{
v___x_624_ = v_p_609_;
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_p_622_);
lean_inc(v_v_621_);
lean_inc(v_k_620_);
lean_dec(v_p_609_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = lean_int_mul(v_k_610_, v_k_620_);
lean_dec(v_k_620_);
v___x_627_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_622_, v_k_610_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_627_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27___boxed(lean_object* v_p_632_, lean_object* v_k_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_632_, v_k_633_);
lean_dec(v_k_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul(lean_object* v_p_635_, lean_object* v_k_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_638_ = lean_int_dec_eq(v_k_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_635_, v_k_636_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
lean_dec_ref(v_p_635_);
v___x_640_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__1, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul___boxed(lean_object* v_p_641_, lean_object* v_k_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Int_Internal_Linear_Poly_mul(v_p_641_, v_k_642_);
lean_dec(v_k_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object* v_fuel_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
lean_object* v_zero_647_; uint8_t v_isZero_648_; 
v_zero_647_ = lean_unsigned_to_nat(0u);
v_isZero_648_ = lean_nat_dec_eq(v_fuel_644_, v_zero_647_);
if (v_isZero_648_ == 1)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v_h__2_646_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_apply_1(v_h__1_645_, v___x_649_);
return v___x_650_;
}
else
{
lean_object* v_one_651_; lean_object* v_n_652_; lean_object* v___x_653_; 
lean_dec(v_h__1_645_);
v_one_651_ = lean_unsigned_to_nat(1u);
v_n_652_ = lean_nat_sub(v_fuel_644_, v_one_651_);
v___x_653_ = lean_apply_1(v_h__2_646_, v_n_652_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object* v_fuel_654_, lean_object* v_h__1_655_, lean_object* v_h__2_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(v_fuel_654_, v_h__1_655_, v_h__2_656_);
lean_dec(v_fuel_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(lean_object* v_motive_658_, lean_object* v_fuel_659_, lean_object* v_h__1_660_, lean_object* v_h__2_661_){
_start:
{
lean_object* v_zero_662_; uint8_t v_isZero_663_; 
v_zero_662_ = lean_unsigned_to_nat(0u);
v_isZero_663_ = lean_nat_dec_eq(v_fuel_659_, v_zero_662_);
if (v_isZero_663_ == 1)
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_661_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_apply_1(v_h__1_660_, v___x_664_);
return v___x_665_;
}
else
{
lean_object* v_one_666_; lean_object* v_n_667_; lean_object* v___x_668_; 
lean_dec(v_h__1_660_);
v_one_666_ = lean_unsigned_to_nat(1u);
v_n_667_ = lean_nat_sub(v_fuel_659_, v_one_666_);
v___x_668_ = lean_apply_1(v_h__2_661_, v_n_667_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object* v_motive_669_, lean_object* v_fuel_670_, lean_object* v_h__1_671_, lean_object* v_h__2_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(v_motive_669_, v_fuel_670_, v_h__1_671_, v_h__2_672_);
lean_dec(v_fuel_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object* v_p_u2081_674_, lean_object* v_p_u2082_675_, lean_object* v_h__1_676_, lean_object* v_h__2_677_, lean_object* v_h__3_678_, lean_object* v_h__4_679_){
_start:
{
if (lean_obj_tag(v_p_u2081_674_) == 0)
{
lean_dec(v_h__4_679_);
lean_dec(v_h__3_678_);
if (lean_obj_tag(v_p_u2082_675_) == 0)
{
lean_object* v_k_680_; lean_object* v_k_681_; lean_object* v___x_682_; 
lean_dec(v_h__2_677_);
v_k_680_ = lean_ctor_get(v_p_u2081_674_, 0);
lean_inc(v_k_680_);
lean_dec_ref_known(v_p_u2081_674_, 1);
v_k_681_ = lean_ctor_get(v_p_u2082_675_, 0);
lean_inc(v_k_681_);
lean_dec_ref_known(v_p_u2082_675_, 1);
v___x_682_ = lean_apply_2(v_h__1_676_, v_k_680_, v_k_681_);
return v___x_682_;
}
else
{
lean_object* v_k_683_; lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_p_686_; lean_object* v___x_687_; 
lean_dec(v_h__1_676_);
v_k_683_ = lean_ctor_get(v_p_u2081_674_, 0);
lean_inc(v_k_683_);
lean_dec_ref_known(v_p_u2081_674_, 1);
v_k_684_ = lean_ctor_get(v_p_u2082_675_, 0);
lean_inc(v_k_684_);
v_v_685_ = lean_ctor_get(v_p_u2082_675_, 1);
lean_inc(v_v_685_);
v_p_686_ = lean_ctor_get(v_p_u2082_675_, 2);
lean_inc_ref(v_p_686_);
lean_dec_ref_known(v_p_u2082_675_, 3);
v___x_687_ = lean_apply_4(v_h__2_677_, v_k_683_, v_k_684_, v_v_685_, v_p_686_);
return v___x_687_;
}
}
else
{
lean_dec(v_h__2_677_);
lean_dec(v_h__1_676_);
if (lean_obj_tag(v_p_u2082_675_) == 0)
{
lean_object* v_k_688_; lean_object* v_v_689_; lean_object* v_p_690_; lean_object* v_k_691_; lean_object* v___x_692_; 
lean_dec(v_h__4_679_);
v_k_688_ = lean_ctor_get(v_p_u2081_674_, 0);
lean_inc(v_k_688_);
v_v_689_ = lean_ctor_get(v_p_u2081_674_, 1);
lean_inc(v_v_689_);
v_p_690_ = lean_ctor_get(v_p_u2081_674_, 2);
lean_inc_ref(v_p_690_);
lean_dec_ref_known(v_p_u2081_674_, 3);
v_k_691_ = lean_ctor_get(v_p_u2082_675_, 0);
lean_inc(v_k_691_);
lean_dec_ref_known(v_p_u2082_675_, 1);
v___x_692_ = lean_apply_4(v_h__3_678_, v_k_688_, v_v_689_, v_p_690_, v_k_691_);
return v___x_692_;
}
else
{
lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v_p_695_; lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_p_698_; lean_object* v___x_699_; 
lean_dec(v_h__3_678_);
v_k_693_ = lean_ctor_get(v_p_u2081_674_, 0);
lean_inc(v_k_693_);
v_v_694_ = lean_ctor_get(v_p_u2081_674_, 1);
lean_inc(v_v_694_);
v_p_695_ = lean_ctor_get(v_p_u2081_674_, 2);
lean_inc_ref(v_p_695_);
lean_dec_ref_known(v_p_u2081_674_, 3);
v_k_696_ = lean_ctor_get(v_p_u2082_675_, 0);
lean_inc(v_k_696_);
v_v_697_ = lean_ctor_get(v_p_u2082_675_, 1);
lean_inc(v_v_697_);
v_p_698_ = lean_ctor_get(v_p_u2082_675_, 2);
lean_inc_ref(v_p_698_);
lean_dec_ref_known(v_p_u2082_675_, 3);
v___x_699_ = lean_apply_6(v_h__4_679_, v_k_693_, v_v_694_, v_p_695_, v_k_696_, v_v_697_, v_p_698_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter(lean_object* v_motive_700_, lean_object* v_p_u2081_701_, lean_object* v_p_u2082_702_, lean_object* v_h__1_703_, lean_object* v_h__2_704_, lean_object* v_h__3_705_, lean_object* v_h__4_706_){
_start:
{
if (lean_obj_tag(v_p_u2081_701_) == 0)
{
lean_dec(v_h__4_706_);
lean_dec(v_h__3_705_);
if (lean_obj_tag(v_p_u2082_702_) == 0)
{
lean_object* v_k_707_; lean_object* v_k_708_; lean_object* v___x_709_; 
lean_dec(v_h__2_704_);
v_k_707_ = lean_ctor_get(v_p_u2081_701_, 0);
lean_inc(v_k_707_);
lean_dec_ref_known(v_p_u2081_701_, 1);
v_k_708_ = lean_ctor_get(v_p_u2082_702_, 0);
lean_inc(v_k_708_);
lean_dec_ref_known(v_p_u2082_702_, 1);
v___x_709_ = lean_apply_2(v_h__1_703_, v_k_707_, v_k_708_);
return v___x_709_;
}
else
{
lean_object* v_k_710_; lean_object* v_k_711_; lean_object* v_v_712_; lean_object* v_p_713_; lean_object* v___x_714_; 
lean_dec(v_h__1_703_);
v_k_710_ = lean_ctor_get(v_p_u2081_701_, 0);
lean_inc(v_k_710_);
lean_dec_ref_known(v_p_u2081_701_, 1);
v_k_711_ = lean_ctor_get(v_p_u2082_702_, 0);
lean_inc(v_k_711_);
v_v_712_ = lean_ctor_get(v_p_u2082_702_, 1);
lean_inc(v_v_712_);
v_p_713_ = lean_ctor_get(v_p_u2082_702_, 2);
lean_inc_ref(v_p_713_);
lean_dec_ref_known(v_p_u2082_702_, 3);
v___x_714_ = lean_apply_4(v_h__2_704_, v_k_710_, v_k_711_, v_v_712_, v_p_713_);
return v___x_714_;
}
}
else
{
lean_dec(v_h__2_704_);
lean_dec(v_h__1_703_);
if (lean_obj_tag(v_p_u2082_702_) == 0)
{
lean_object* v_k_715_; lean_object* v_v_716_; lean_object* v_p_717_; lean_object* v_k_718_; lean_object* v___x_719_; 
lean_dec(v_h__4_706_);
v_k_715_ = lean_ctor_get(v_p_u2081_701_, 0);
lean_inc(v_k_715_);
v_v_716_ = lean_ctor_get(v_p_u2081_701_, 1);
lean_inc(v_v_716_);
v_p_717_ = lean_ctor_get(v_p_u2081_701_, 2);
lean_inc_ref(v_p_717_);
lean_dec_ref_known(v_p_u2081_701_, 3);
v_k_718_ = lean_ctor_get(v_p_u2082_702_, 0);
lean_inc(v_k_718_);
lean_dec_ref_known(v_p_u2082_702_, 1);
v___x_719_ = lean_apply_4(v_h__3_705_, v_k_715_, v_v_716_, v_p_717_, v_k_718_);
return v___x_719_;
}
else
{
lean_object* v_k_720_; lean_object* v_v_721_; lean_object* v_p_722_; lean_object* v_k_723_; lean_object* v_v_724_; lean_object* v_p_725_; lean_object* v___x_726_; 
lean_dec(v_h__3_705_);
v_k_720_ = lean_ctor_get(v_p_u2081_701_, 0);
lean_inc(v_k_720_);
v_v_721_ = lean_ctor_get(v_p_u2081_701_, 1);
lean_inc(v_v_721_);
v_p_722_ = lean_ctor_get(v_p_u2081_701_, 2);
lean_inc_ref(v_p_722_);
lean_dec_ref_known(v_p_u2081_701_, 3);
v_k_723_ = lean_ctor_get(v_p_u2082_702_, 0);
lean_inc(v_k_723_);
v_v_724_ = lean_ctor_get(v_p_u2082_702_, 1);
lean_inc(v_v_724_);
v_p_725_ = lean_ctor_get(v_p_u2082_702_, 2);
lean_inc_ref(v_p_725_);
lean_dec_ref_known(v_p_u2082_702_, 3);
v___x_726_ = lean_apply_6(v_h__4_706_, v_k_720_, v_v_721_, v_p_722_, v_k_723_, v_v_724_, v_p_725_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* v_x_727_, lean_object* v_h__1_728_, lean_object* v_h__2_729_, lean_object* v_h__3_730_, lean_object* v_h__4_731_, lean_object* v_h__5_732_, lean_object* v_h__6_733_, lean_object* v_h__7_734_){
_start:
{
switch(lean_obj_tag(v_x_727_))
{
case 0:
{
lean_object* v_v_735_; lean_object* v___x_736_; 
lean_dec(v_h__7_734_);
lean_dec(v_h__6_733_);
lean_dec(v_h__5_732_);
lean_dec(v_h__4_731_);
lean_dec(v_h__3_730_);
lean_dec(v_h__2_729_);
v_v_735_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_v_735_);
lean_dec_ref_known(v_x_727_, 1);
v___x_736_ = lean_apply_1(v_h__1_728_, v_v_735_);
return v___x_736_;
}
case 1:
{
lean_object* v_i_737_; lean_object* v___x_738_; 
lean_dec(v_h__7_734_);
lean_dec(v_h__6_733_);
lean_dec(v_h__5_732_);
lean_dec(v_h__4_731_);
lean_dec(v_h__3_730_);
lean_dec(v_h__1_728_);
v_i_737_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_i_737_);
lean_dec_ref_known(v_x_727_, 1);
v___x_738_ = lean_apply_1(v_h__2_729_, v_i_737_);
return v___x_738_;
}
case 2:
{
lean_object* v_a_739_; lean_object* v_b_740_; lean_object* v___x_741_; 
lean_dec(v_h__7_734_);
lean_dec(v_h__6_733_);
lean_dec(v_h__5_732_);
lean_dec(v_h__4_731_);
lean_dec(v_h__2_729_);
lean_dec(v_h__1_728_);
v_a_739_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_a_739_);
v_b_740_ = lean_ctor_get(v_x_727_, 1);
lean_inc_ref(v_b_740_);
lean_dec_ref_known(v_x_727_, 2);
v___x_741_ = lean_apply_2(v_h__3_730_, v_a_739_, v_b_740_);
return v___x_741_;
}
case 3:
{
lean_object* v_a_742_; lean_object* v_b_743_; lean_object* v___x_744_; 
lean_dec(v_h__7_734_);
lean_dec(v_h__6_733_);
lean_dec(v_h__5_732_);
lean_dec(v_h__3_730_);
lean_dec(v_h__2_729_);
lean_dec(v_h__1_728_);
v_a_742_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_a_742_);
v_b_743_ = lean_ctor_get(v_x_727_, 1);
lean_inc_ref(v_b_743_);
lean_dec_ref_known(v_x_727_, 2);
v___x_744_ = lean_apply_2(v_h__4_731_, v_a_742_, v_b_743_);
return v___x_744_;
}
case 4:
{
lean_object* v_a_745_; lean_object* v___x_746_; 
lean_dec(v_h__6_733_);
lean_dec(v_h__5_732_);
lean_dec(v_h__4_731_);
lean_dec(v_h__3_730_);
lean_dec(v_h__2_729_);
lean_dec(v_h__1_728_);
v_a_745_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_a_745_);
lean_dec_ref_known(v_x_727_, 1);
v___x_746_ = lean_apply_1(v_h__7_734_, v_a_745_);
return v___x_746_;
}
case 5:
{
lean_object* v_k_747_; lean_object* v_a_748_; lean_object* v___x_749_; 
lean_dec(v_h__7_734_);
lean_dec(v_h__6_733_);
lean_dec(v_h__4_731_);
lean_dec(v_h__3_730_);
lean_dec(v_h__2_729_);
lean_dec(v_h__1_728_);
v_k_747_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_k_747_);
v_a_748_ = lean_ctor_get(v_x_727_, 1);
lean_inc_ref(v_a_748_);
lean_dec_ref_known(v_x_727_, 2);
v___x_749_ = lean_apply_2(v_h__5_732_, v_k_747_, v_a_748_);
return v___x_749_;
}
default: 
{
lean_object* v_a_750_; lean_object* v_k_751_; lean_object* v___x_752_; 
lean_dec(v_h__7_734_);
lean_dec(v_h__5_732_);
lean_dec(v_h__4_731_);
lean_dec(v_h__3_730_);
lean_dec(v_h__2_729_);
lean_dec(v_h__1_728_);
v_a_750_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_a_750_);
v_k_751_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_k_751_);
lean_dec_ref_known(v_x_727_, 2);
v___x_752_ = lean_apply_2(v_h__6_733_, v_a_750_, v_k_751_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* v_motive_753_, lean_object* v_x_754_, lean_object* v_h__1_755_, lean_object* v_h__2_756_, lean_object* v_h__3_757_, lean_object* v_h__4_758_, lean_object* v_h__5_759_, lean_object* v_h__6_760_, lean_object* v_h__7_761_){
_start:
{
switch(lean_obj_tag(v_x_754_))
{
case 0:
{
lean_object* v_v_762_; lean_object* v___x_763_; 
lean_dec(v_h__7_761_);
lean_dec(v_h__6_760_);
lean_dec(v_h__5_759_);
lean_dec(v_h__4_758_);
lean_dec(v_h__3_757_);
lean_dec(v_h__2_756_);
v_v_762_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_v_762_);
lean_dec_ref_known(v_x_754_, 1);
v___x_763_ = lean_apply_1(v_h__1_755_, v_v_762_);
return v___x_763_;
}
case 1:
{
lean_object* v_i_764_; lean_object* v___x_765_; 
lean_dec(v_h__7_761_);
lean_dec(v_h__6_760_);
lean_dec(v_h__5_759_);
lean_dec(v_h__4_758_);
lean_dec(v_h__3_757_);
lean_dec(v_h__1_755_);
v_i_764_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_i_764_);
lean_dec_ref_known(v_x_754_, 1);
v___x_765_ = lean_apply_1(v_h__2_756_, v_i_764_);
return v___x_765_;
}
case 2:
{
lean_object* v_a_766_; lean_object* v_b_767_; lean_object* v___x_768_; 
lean_dec(v_h__7_761_);
lean_dec(v_h__6_760_);
lean_dec(v_h__5_759_);
lean_dec(v_h__4_758_);
lean_dec(v_h__2_756_);
lean_dec(v_h__1_755_);
v_a_766_ = lean_ctor_get(v_x_754_, 0);
lean_inc_ref(v_a_766_);
v_b_767_ = lean_ctor_get(v_x_754_, 1);
lean_inc_ref(v_b_767_);
lean_dec_ref_known(v_x_754_, 2);
v___x_768_ = lean_apply_2(v_h__3_757_, v_a_766_, v_b_767_);
return v___x_768_;
}
case 3:
{
lean_object* v_a_769_; lean_object* v_b_770_; lean_object* v___x_771_; 
lean_dec(v_h__7_761_);
lean_dec(v_h__6_760_);
lean_dec(v_h__5_759_);
lean_dec(v_h__3_757_);
lean_dec(v_h__2_756_);
lean_dec(v_h__1_755_);
v_a_769_ = lean_ctor_get(v_x_754_, 0);
lean_inc_ref(v_a_769_);
v_b_770_ = lean_ctor_get(v_x_754_, 1);
lean_inc_ref(v_b_770_);
lean_dec_ref_known(v_x_754_, 2);
v___x_771_ = lean_apply_2(v_h__4_758_, v_a_769_, v_b_770_);
return v___x_771_;
}
case 4:
{
lean_object* v_a_772_; lean_object* v___x_773_; 
lean_dec(v_h__6_760_);
lean_dec(v_h__5_759_);
lean_dec(v_h__4_758_);
lean_dec(v_h__3_757_);
lean_dec(v_h__2_756_);
lean_dec(v_h__1_755_);
v_a_772_ = lean_ctor_get(v_x_754_, 0);
lean_inc_ref(v_a_772_);
lean_dec_ref_known(v_x_754_, 1);
v___x_773_ = lean_apply_1(v_h__7_761_, v_a_772_);
return v___x_773_;
}
case 5:
{
lean_object* v_k_774_; lean_object* v_a_775_; lean_object* v___x_776_; 
lean_dec(v_h__7_761_);
lean_dec(v_h__6_760_);
lean_dec(v_h__4_758_);
lean_dec(v_h__3_757_);
lean_dec(v_h__2_756_);
lean_dec(v_h__1_755_);
v_k_774_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_k_774_);
v_a_775_ = lean_ctor_get(v_x_754_, 1);
lean_inc_ref(v_a_775_);
lean_dec_ref_known(v_x_754_, 2);
v___x_776_ = lean_apply_2(v_h__5_759_, v_k_774_, v_a_775_);
return v___x_776_;
}
default: 
{
lean_object* v_a_777_; lean_object* v_k_778_; lean_object* v___x_779_; 
lean_dec(v_h__7_761_);
lean_dec(v_h__5_759_);
lean_dec(v_h__4_758_);
lean_dec(v_h__3_757_);
lean_dec(v_h__2_756_);
lean_dec(v_h__1_755_);
v_a_777_ = lean_ctor_get(v_x_754_, 0);
lean_inc_ref(v_a_777_);
v_k_778_ = lean_ctor_get(v_x_754_, 1);
lean_inc(v_k_778_);
lean_dec_ref_known(v_x_754_, 2);
v___x_779_ = lean_apply_2(v_h__6_760_, v_a_777_, v_k_778_);
return v___x_779_;
}
}
}
}
uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object* v_p_780_){
_start:
{
if (lean_obj_tag(v_p_780_) == 0)
{
lean_object* v_k_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_k_781_ = lean_ctor_get(v_p_780_, 0);
v___x_782_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_783_ = lean_int_dec_eq(v_k_781_, v___x_782_);
if (v___x_783_ == 0)
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
}
else
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isUnsatEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_780_ = stack[0].m_obj;
uint8_t v_res_787_;
v_res_787_ = l_Int_Internal_Linear_Poly_isUnsatEq(v_p_780_);
stack->m_num = v_res_787_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatEq___boxed(lean_object* v_p_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Int_Internal_Linear_Poly_isUnsatEq(v_p_788_);
lean_dec_ref(v_p_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object* v_p_791_){
_start:
{
if (lean_obj_tag(v_p_791_) == 0)
{
lean_object* v_k_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_k_792_ = lean_ctor_get(v_p_791_, 0);
v___x_793_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_794_ = lean_int_dec_eq(v_k_792_, v___x_793_);
return v___x_794_;
}
else
{
uint8_t v___x_795_; 
v___x_795_ = 0;
return v___x_795_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isValidEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_791_ = stack[0].m_obj;
uint8_t v_res_796_;
v_res_796_ = l_Int_Internal_Linear_Poly_isValidEq(v_p_791_);
stack->m_num = v_res_796_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidEq___boxed(lean_object* v_p_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Int_Internal_Linear_Poly_isValidEq(v_p_797_);
lean_dec_ref(v_p_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* v_p_800_, lean_object* v_h__1_801_, lean_object* v_h__2_802_){
_start:
{
if (lean_obj_tag(v_p_800_) == 0)
{
lean_object* v_k_803_; lean_object* v___x_804_; 
lean_dec(v_h__2_802_);
v_k_803_ = lean_ctor_get(v_p_800_, 0);
lean_inc(v_k_803_);
lean_dec_ref_known(v_p_800_, 1);
v___x_804_ = lean_apply_1(v_h__1_801_, v_k_803_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; 
lean_dec(v_h__1_801_);
v___x_805_ = lean_apply_2(v_h__2_802_, v_p_800_, lean_box(0));
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* v_motive_806_, lean_object* v_p_807_, lean_object* v_h__1_808_, lean_object* v_h__2_809_){
_start:
{
if (lean_obj_tag(v_p_807_) == 0)
{
lean_object* v_k_810_; lean_object* v___x_811_; 
lean_dec(v_h__2_809_);
v_k_810_ = lean_ctor_get(v_p_807_, 0);
lean_inc(v_k_810_);
lean_dec_ref_known(v_p_807_, 1);
v___x_811_ = lean_apply_1(v_h__1_808_, v_k_810_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; 
lean_dec(v_h__1_808_);
v___x_812_ = lean_apply_2(v_h__2_809_, v_p_807_, lean_box(0));
return v___x_812_;
}
}
}
uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object* v_p_813_){
_start:
{
if (lean_obj_tag(v_p_813_) == 0)
{
lean_object* v_k_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_k_814_ = lean_ctor_get(v_p_813_, 0);
v___x_815_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_816_ = lean_int_dec_lt(v___x_815_, v_k_814_);
return v___x_816_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isUnsatLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_813_ = stack[0].m_obj;
uint8_t v_res_818_;
v_res_818_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_813_);
stack->m_num = v_res_818_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatLe___boxed(lean_object* v_p_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_819_);
lean_dec_ref(v_p_819_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object* v_p_822_){
_start:
{
if (lean_obj_tag(v_p_822_) == 0)
{
lean_object* v_k_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_k_823_ = lean_ctor_get(v_p_822_, 0);
v___x_824_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_825_ = lean_int_dec_le(v_k_823_, v___x_824_);
return v___x_825_;
}
else
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isValidLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_822_ = stack[0].m_obj;
uint8_t v_res_827_;
v_res_827_ = l_Int_Internal_Linear_Poly_isValidLe(v_p_822_);
stack->m_num = v_res_827_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidLe___boxed(lean_object* v_p_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_Int_Internal_Linear_Poly_isValidLe(v_p_828_);
lean_dec_ref(v_p_828_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(lean_object* v_a_831_, lean_object* v_b_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = l_Int_gcd(v_a_831_, v_b_832_);
v___x_834_ = lean_nat_to_int(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd___boxed(lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(v_a_835_, v_b_836_);
lean_dec(v_b_836_);
lean_dec(v_a_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
return v_x_839_;
}
else
{
lean_object* v_k_840_; lean_object* v_p_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_k_840_ = lean_ctor_get(v_x_838_, 0);
v_p_841_ = lean_ctor_get(v_x_838_, 2);
v___x_842_ = l_Int_gcd(v_k_840_, v_x_839_);
lean_dec(v_x_839_);
v___x_843_ = lean_nat_to_int(v___x_842_);
v_x_838_ = v_p_841_;
v_x_839_ = v___x_843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs___boxed(lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_x_845_, v_x_846_);
lean_dec_ref(v_x_845_);
return v_res_847_;
}
}
uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object* v_k_848_, lean_object* v_p_849_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_850_ = l_Int_Internal_Linear_Poly_getConst(v_p_849_);
v___x_851_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_849_, v_k_848_);
v___x_852_ = lean_int_emod(v___x_850_, v___x_851_);
lean_dec(v___x_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_854_ = lean_int_dec_eq(v___x_852_, v___x_853_);
lean_dec(v___x_852_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
v___x_855_ = 1;
return v___x_855_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = 0;
return v___x_856_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isUnsatDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_848_ = stack[0].m_obj;
lean_object* v_p_849_ = stack[1].m_obj;
uint8_t v_res_857_;
v_res_857_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_k_848_, v_p_849_);
stack->m_num = v_res_857_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDvd___boxed(lean_object* v_k_858_, lean_object* v_p_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_k_858_, v_p_859_);
lean_dec_ref(v_p_859_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object* v_p_u2081_862_, lean_object* v_p_u2082_863_, lean_object* v_h__1_864_, lean_object* v_h__2_865_){
_start:
{
if (lean_obj_tag(v_p_u2081_862_) == 1)
{
if (lean_obj_tag(v_p_u2082_863_) == 1)
{
lean_object* v_k_866_; lean_object* v_v_867_; lean_object* v_p_868_; lean_object* v_k_869_; lean_object* v_v_870_; lean_object* v_p_871_; lean_object* v___x_872_; 
lean_dec(v_h__2_865_);
v_k_866_ = lean_ctor_get(v_p_u2081_862_, 0);
lean_inc(v_k_866_);
v_v_867_ = lean_ctor_get(v_p_u2081_862_, 1);
lean_inc(v_v_867_);
v_p_868_ = lean_ctor_get(v_p_u2081_862_, 2);
lean_inc_ref(v_p_868_);
lean_dec_ref_known(v_p_u2081_862_, 3);
v_k_869_ = lean_ctor_get(v_p_u2082_863_, 0);
lean_inc(v_k_869_);
v_v_870_ = lean_ctor_get(v_p_u2082_863_, 1);
lean_inc(v_v_870_);
v_p_871_ = lean_ctor_get(v_p_u2082_863_, 2);
lean_inc_ref(v_p_871_);
lean_dec_ref_known(v_p_u2082_863_, 3);
v___x_872_ = lean_apply_6(v_h__1_864_, v_k_866_, v_v_867_, v_p_868_, v_k_869_, v_v_870_, v_p_871_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; 
lean_dec(v_h__1_864_);
v___x_873_ = lean_apply_3(v_h__2_865_, v_p_u2081_862_, v_p_u2082_863_, lean_box(0));
return v___x_873_;
}
}
else
{
lean_object* v___x_874_; 
lean_dec(v_h__1_864_);
v___x_874_ = lean_apply_3(v_h__2_865_, v_p_u2081_862_, v_p_u2082_863_, lean_box(0));
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object* v_motive_875_, lean_object* v_p_u2081_876_, lean_object* v_p_u2082_877_, lean_object* v_h__1_878_, lean_object* v_h__2_879_){
_start:
{
if (lean_obj_tag(v_p_u2081_876_) == 1)
{
if (lean_obj_tag(v_p_u2082_877_) == 1)
{
lean_object* v_k_880_; lean_object* v_v_881_; lean_object* v_p_882_; lean_object* v_k_883_; lean_object* v_v_884_; lean_object* v_p_885_; lean_object* v___x_886_; 
lean_dec(v_h__2_879_);
v_k_880_ = lean_ctor_get(v_p_u2081_876_, 0);
lean_inc(v_k_880_);
v_v_881_ = lean_ctor_get(v_p_u2081_876_, 1);
lean_inc(v_v_881_);
v_p_882_ = lean_ctor_get(v_p_u2081_876_, 2);
lean_inc_ref(v_p_882_);
lean_dec_ref_known(v_p_u2081_876_, 3);
v_k_883_ = lean_ctor_get(v_p_u2082_877_, 0);
lean_inc(v_k_883_);
v_v_884_ = lean_ctor_get(v_p_u2082_877_, 1);
lean_inc(v_v_884_);
v_p_885_ = lean_ctor_get(v_p_u2082_877_, 2);
lean_inc_ref(v_p_885_);
lean_dec_ref_known(v_p_u2082_877_, 3);
v___x_886_ = lean_apply_6(v_h__1_878_, v_k_880_, v_v_881_, v_p_882_, v_k_883_, v_v_884_, v_p_885_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; 
lean_dec(v_h__1_878_);
v___x_887_ = lean_apply_3(v_h__2_879_, v_p_u2081_876_, v_p_u2082_877_, lean_box(0));
return v___x_887_;
}
}
else
{
lean_object* v___x_888_; 
lean_dec(v_h__1_878_);
v___x_888_ = lean_apply_3(v_h__2_879_, v_p_u2081_876_, v_p_u2082_877_, lean_box(0));
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object* v_p_889_){
_start:
{
if (lean_obj_tag(v_p_889_) == 1)
{
lean_object* v_k_890_; 
v_k_890_ = lean_ctor_get(v_p_889_, 0);
lean_inc(v_k_890_);
return v_k_890_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff___boxed(lean_object* v_p_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_892_);
lean_dec_ref(v_p_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object* v_p_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_p_894_) == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
return v___x_896_;
}
else
{
lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_p_899_; uint8_t v___x_900_; 
v_k_897_ = lean_ctor_get(v_p_894_, 0);
v_v_898_ = lean_ctor_get(v_p_894_, 1);
v_p_899_ = lean_ctor_get(v_p_894_, 2);
v___x_900_ = lean_nat_dec_eq(v_x_895_, v_v_898_);
if (v___x_900_ == 0)
{
v_p_894_ = v_p_899_;
goto _start;
}
else
{
lean_inc(v_k_897_);
return v_k_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff___boxed(lean_object* v_p_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Int_Internal_Linear_Poly_coeff(v_p_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec_ref(v_p_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs(lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_nat_abs(v_x_905_);
v___x_907_ = lean_nat_to_int(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs___boxed(lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Int_Internal_Linear_abs(v_x_908_);
lean_dec(v_x_908_);
return v_res_909_;
}
}
uint8_t l_Int_Internal_Linear_Poly_isUnsatDiseq(lean_object* v_p_910_){
_start:
{
if (lean_obj_tag(v_p_910_) == 0)
{
lean_object* v_k_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_k_911_ = lean_ctor_get(v_p_910_, 0);
v___x_912_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_913_ = lean_int_dec_eq(v_k_911_, v___x_912_);
return v___x_913_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = 0;
return v___x_914_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isUnsatDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_910_ = stack[0].m_obj;
uint8_t v_res_915_;
v_res_915_ = l_Int_Internal_Linear_Poly_isUnsatDiseq(v_p_910_);
stack->m_num = v_res_915_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDiseq___boxed(lean_object* v_p_916_){
_start:
{
uint8_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_Int_Internal_Linear_Poly_isUnsatDiseq(v_p_916_);
lean_dec_ref(v_p_916_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail(lean_object* v_p_919_){
_start:
{
if (lean_obj_tag(v_p_919_) == 1)
{
lean_object* v_p_920_; 
v_p_920_ = lean_ctor_get(v_p_919_, 2);
lean_inc_ref(v_p_920_);
return v_p_920_;
}
else
{
lean_inc_ref(v_p_919_);
return v_p_919_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail___boxed(lean_object* v_p_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Int_Internal_Linear_Poly_tail(v_p_921_);
lean_dec_ref(v_p_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object* v_p_923_, lean_object* v_h__1_924_, lean_object* v_h__2_925_){
_start:
{
if (lean_obj_tag(v_p_923_) == 1)
{
lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_p_928_; lean_object* v___x_929_; 
lean_dec(v_h__2_925_);
v_k_926_ = lean_ctor_get(v_p_923_, 0);
lean_inc(v_k_926_);
v_v_927_ = lean_ctor_get(v_p_923_, 1);
lean_inc(v_v_927_);
v_p_928_ = lean_ctor_get(v_p_923_, 2);
lean_inc_ref(v_p_928_);
lean_dec_ref_known(v_p_923_, 3);
v___x_929_ = lean_apply_3(v_h__1_924_, v_k_926_, v_v_927_, v_p_928_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; 
lean_dec(v_h__1_924_);
v___x_930_ = lean_apply_2(v_h__2_925_, v_p_923_, lean_box(0));
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter(lean_object* v_motive_931_, lean_object* v_p_932_, lean_object* v_h__1_933_, lean_object* v_h__2_934_){
_start:
{
if (lean_obj_tag(v_p_932_) == 1)
{
lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_p_937_; lean_object* v___x_938_; 
lean_dec(v_h__2_934_);
v_k_935_ = lean_ctor_get(v_p_932_, 0);
lean_inc(v_k_935_);
v_v_936_ = lean_ctor_get(v_p_932_, 1);
lean_inc(v_v_936_);
v_p_937_ = lean_ctor_get(v_p_932_, 2);
lean_inc_ref(v_p_937_);
lean_dec_ref_known(v_p_932_, 3);
v___x_938_ = lean_apply_3(v_h__1_933_, v_k_935_, v_v_936_, v_p_937_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; 
lean_dec(v_h__1_933_);
v___x_939_ = lean_apply_2(v_h__2_934_, v_p_932_, lean_box(0));
return v___x_939_;
}
}
}
uint8_t l_Int_Internal_Linear_Poly_casesOnAdd(lean_object* v_p_940_, lean_object* v_k_941_){
_start:
{
if (lean_obj_tag(v_p_940_) == 0)
{
uint8_t v___x_942_; 
lean_dec_ref_known(v_p_940_, 1);
lean_dec_ref(v_k_941_);
v___x_942_ = 0;
return v___x_942_;
}
else
{
lean_object* v_a_943_; lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_a_943_ = lean_ctor_get(v_p_940_, 0);
lean_inc(v_a_943_);
v_a_944_ = lean_ctor_get(v_p_940_, 1);
lean_inc(v_a_944_);
v_a_945_ = lean_ctor_get(v_p_940_, 2);
lean_inc_ref(v_a_945_);
lean_dec_ref_known(v_p_940_, 3);
v___x_946_ = lean_apply_3(v_k_941_, v_a_943_, v_a_944_, v_a_945_);
v___x_947_ = lean_unbox(v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_casesOnAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_940_ = stack[0].m_obj;
lean_object* v_k_941_ = stack[1].m_obj;
uint8_t v_res_948_;
v_res_948_ = l_Int_Internal_Linear_Poly_casesOnAdd(v_p_940_, v_k_941_);
stack->m_num = v_res_948_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnAdd___boxed(lean_object* v_p_949_, lean_object* v_k_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Int_Internal_Linear_Poly_casesOnAdd(v_p_949_, v_k_950_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
uint8_t l_Int_Internal_Linear_Poly_casesOnNum(lean_object* v_p_953_, lean_object* v_k_954_){
_start:
{
if (lean_obj_tag(v_p_953_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_a_955_ = lean_ctor_get(v_p_953_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v_p_953_, 1);
v___x_956_ = lean_apply_1(v_k_954_, v_a_955_);
v___x_957_ = lean_unbox(v___x_956_);
return v___x_957_;
}
else
{
uint8_t v___x_958_; 
lean_dec_ref_known(v_p_953_, 3);
lean_dec_ref(v_k_954_);
v___x_958_ = 0;
return v___x_958_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_casesOnNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_953_ = stack[0].m_obj;
lean_object* v_k_954_ = stack[1].m_obj;
uint8_t v_res_959_;
v_res_959_ = l_Int_Internal_Linear_Poly_casesOnNum(v_p_953_, v_k_954_);
stack->m_num = v_res_959_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnNum___boxed(lean_object* v_p_960_, lean_object* v_k_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Int_Internal_Linear_Poly_casesOnNum(v_p_960_, v_k_961_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
uint8_t l_Int_Internal_Linear_emod__le__cert(lean_object* v_y_964_, lean_object* v_n_965_){
_start:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_967_ = lean_int_dec_eq(v_y_964_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_968_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_969_ = lean_nat_abs(v_y_964_);
v___x_970_ = lean_nat_to_int(v___x_969_);
v___x_971_ = lean_int_sub(v___x_968_, v___x_970_);
lean_dec(v___x_970_);
v___x_972_ = lean_int_dec_eq(v_n_965_, v___x_971_);
lean_dec(v___x_971_);
return v___x_972_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = 0;
return v___x_973_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_emod__le__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_964_ = stack[0].m_obj;
lean_object* v_n_965_ = stack[1].m_obj;
uint8_t v_res_974_;
v_res_974_ = l_Int_Internal_Linear_emod__le__cert(v_y_964_, v_n_965_);
stack->m_num = v_res_974_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_emod__le__cert___boxed(lean_object* v_y_975_, lean_object* v_n_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Int_Internal_Linear_emod__le__cert(v_y_975_, v_n_976_);
lean_dec(v_n_976_);
lean_dec(v_y_975_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
uint8_t l_Int_Internal_Linear_le__of__le__cert(lean_object* v_p_u2081_979_, lean_object* v_p_u2082_980_){
_start:
{
if (lean_obj_tag(v_p_u2081_979_) == 0)
{
if (lean_obj_tag(v_p_u2082_980_) == 0)
{
lean_object* v_k_981_; lean_object* v_k_982_; uint8_t v___x_983_; 
v_k_981_ = lean_ctor_get(v_p_u2081_979_, 0);
v_k_982_ = lean_ctor_get(v_p_u2082_980_, 0);
v___x_983_ = lean_int_dec_le(v_k_982_, v_k_981_);
return v___x_983_;
}
else
{
uint8_t v___x_984_; 
v___x_984_ = 0;
return v___x_984_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_980_) == 0)
{
uint8_t v___x_985_; 
v___x_985_ = 0;
return v___x_985_;
}
else
{
lean_object* v_k_986_; lean_object* v_v_987_; lean_object* v_p_988_; lean_object* v_k_989_; lean_object* v_v_990_; lean_object* v_p_991_; uint8_t v___x_992_; 
v_k_986_ = lean_ctor_get(v_p_u2081_979_, 0);
v_v_987_ = lean_ctor_get(v_p_u2081_979_, 1);
v_p_988_ = lean_ctor_get(v_p_u2081_979_, 2);
v_k_989_ = lean_ctor_get(v_p_u2082_980_, 0);
v_v_990_ = lean_ctor_get(v_p_u2082_980_, 1);
v_p_991_ = lean_ctor_get(v_p_u2082_980_, 2);
v___x_992_ = lean_int_dec_eq(v_k_986_, v_k_989_);
if (v___x_992_ == 0)
{
return v___x_992_;
}
else
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_eq(v_v_987_, v_v_990_);
if (v___x_993_ == 0)
{
return v___x_993_;
}
else
{
v_p_u2081_979_ = v_p_988_;
v_p_u2082_980_ = v_p_991_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_le__of__le__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_979_ = stack[0].m_obj;
lean_object* v_p_u2082_980_ = stack[1].m_obj;
uint8_t v_res_995_;
v_res_995_ = l_Int_Internal_Linear_le__of__le__cert(v_p_u2081_979_, v_p_u2082_980_);
stack->m_num = v_res_995_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_le__of__le__cert___boxed(lean_object* v_p_u2081_996_, lean_object* v_p_u2082_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Int_Internal_Linear_le__of__le__cert(v_p_u2081_996_, v_p_u2082_997_);
lean_dec_ref(v_p_u2082_997_);
lean_dec_ref(v_p_u2081_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object* v_p_u2081_1000_, lean_object* v_p_u2082_1001_, lean_object* v_h__1_1002_, lean_object* v_h__2_1003_, lean_object* v_h__3_1004_, lean_object* v_h__4_1005_){
_start:
{
if (lean_obj_tag(v_p_u2081_1000_) == 0)
{
lean_dec(v_h__4_1005_);
lean_dec(v_h__1_1002_);
if (lean_obj_tag(v_p_u2082_1001_) == 0)
{
lean_object* v_k_1006_; lean_object* v_k_1007_; lean_object* v___x_1008_; 
lean_dec(v_h__2_1003_);
v_k_1006_ = lean_ctor_get(v_p_u2081_1000_, 0);
lean_inc(v_k_1006_);
lean_dec_ref_known(v_p_u2081_1000_, 1);
v_k_1007_ = lean_ctor_get(v_p_u2082_1001_, 0);
lean_inc(v_k_1007_);
lean_dec_ref_known(v_p_u2082_1001_, 1);
v___x_1008_ = lean_apply_2(v_h__3_1004_, v_k_1006_, v_k_1007_);
return v___x_1008_;
}
else
{
lean_object* v_k_1009_; lean_object* v_k_1010_; lean_object* v_v_1011_; lean_object* v_p_1012_; lean_object* v___x_1013_; 
lean_dec(v_h__3_1004_);
v_k_1009_ = lean_ctor_get(v_p_u2081_1000_, 0);
lean_inc(v_k_1009_);
lean_dec_ref_known(v_p_u2081_1000_, 1);
v_k_1010_ = lean_ctor_get(v_p_u2082_1001_, 0);
lean_inc(v_k_1010_);
v_v_1011_ = lean_ctor_get(v_p_u2082_1001_, 1);
lean_inc(v_v_1011_);
v_p_1012_ = lean_ctor_get(v_p_u2082_1001_, 2);
lean_inc_ref(v_p_1012_);
lean_dec_ref_known(v_p_u2082_1001_, 3);
v___x_1013_ = lean_apply_4(v_h__2_1003_, v_k_1009_, v_k_1010_, v_v_1011_, v_p_1012_);
return v___x_1013_;
}
}
else
{
lean_dec(v_h__3_1004_);
lean_dec(v_h__2_1003_);
if (lean_obj_tag(v_p_u2082_1001_) == 0)
{
lean_object* v_k_1014_; lean_object* v_v_1015_; lean_object* v_p_1016_; lean_object* v_k_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__4_1005_);
v_k_1014_ = lean_ctor_get(v_p_u2081_1000_, 0);
lean_inc(v_k_1014_);
v_v_1015_ = lean_ctor_get(v_p_u2081_1000_, 1);
lean_inc(v_v_1015_);
v_p_1016_ = lean_ctor_get(v_p_u2081_1000_, 2);
lean_inc_ref(v_p_1016_);
lean_dec_ref_known(v_p_u2081_1000_, 3);
v_k_1017_ = lean_ctor_get(v_p_u2082_1001_, 0);
lean_inc(v_k_1017_);
lean_dec_ref_known(v_p_u2082_1001_, 1);
v___x_1018_ = lean_apply_4(v_h__1_1002_, v_k_1014_, v_v_1015_, v_p_1016_, v_k_1017_);
return v___x_1018_;
}
else
{
lean_object* v_k_1019_; lean_object* v_v_1020_; lean_object* v_p_1021_; lean_object* v_k_1022_; lean_object* v_v_1023_; lean_object* v_p_1024_; lean_object* v___x_1025_; 
lean_dec(v_h__1_1002_);
v_k_1019_ = lean_ctor_get(v_p_u2081_1000_, 0);
lean_inc(v_k_1019_);
v_v_1020_ = lean_ctor_get(v_p_u2081_1000_, 1);
lean_inc(v_v_1020_);
v_p_1021_ = lean_ctor_get(v_p_u2081_1000_, 2);
lean_inc_ref(v_p_1021_);
lean_dec_ref_known(v_p_u2081_1000_, 3);
v_k_1022_ = lean_ctor_get(v_p_u2082_1001_, 0);
lean_inc(v_k_1022_);
v_v_1023_ = lean_ctor_get(v_p_u2082_1001_, 1);
lean_inc(v_v_1023_);
v_p_1024_ = lean_ctor_get(v_p_u2082_1001_, 2);
lean_inc_ref(v_p_1024_);
lean_dec_ref_known(v_p_u2082_1001_, 3);
v___x_1025_ = lean_apply_6(v_h__4_1005_, v_k_1019_, v_v_1020_, v_p_1021_, v_k_1022_, v_v_1023_, v_p_1024_);
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter(lean_object* v_motive_1026_, lean_object* v_p_u2081_1027_, lean_object* v_p_u2082_1028_, lean_object* v_h__1_1029_, lean_object* v_h__2_1030_, lean_object* v_h__3_1031_, lean_object* v_h__4_1032_){
_start:
{
if (lean_obj_tag(v_p_u2081_1027_) == 0)
{
lean_dec(v_h__4_1032_);
lean_dec(v_h__1_1029_);
if (lean_obj_tag(v_p_u2082_1028_) == 0)
{
lean_object* v_k_1033_; lean_object* v_k_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__2_1030_);
v_k_1033_ = lean_ctor_get(v_p_u2081_1027_, 0);
lean_inc(v_k_1033_);
lean_dec_ref_known(v_p_u2081_1027_, 1);
v_k_1034_ = lean_ctor_get(v_p_u2082_1028_, 0);
lean_inc(v_k_1034_);
lean_dec_ref_known(v_p_u2082_1028_, 1);
v___x_1035_ = lean_apply_2(v_h__3_1031_, v_k_1033_, v_k_1034_);
return v___x_1035_;
}
else
{
lean_object* v_k_1036_; lean_object* v_k_1037_; lean_object* v_v_1038_; lean_object* v_p_1039_; lean_object* v___x_1040_; 
lean_dec(v_h__3_1031_);
v_k_1036_ = lean_ctor_get(v_p_u2081_1027_, 0);
lean_inc(v_k_1036_);
lean_dec_ref_known(v_p_u2081_1027_, 1);
v_k_1037_ = lean_ctor_get(v_p_u2082_1028_, 0);
lean_inc(v_k_1037_);
v_v_1038_ = lean_ctor_get(v_p_u2082_1028_, 1);
lean_inc(v_v_1038_);
v_p_1039_ = lean_ctor_get(v_p_u2082_1028_, 2);
lean_inc_ref(v_p_1039_);
lean_dec_ref_known(v_p_u2082_1028_, 3);
v___x_1040_ = lean_apply_4(v_h__2_1030_, v_k_1036_, v_k_1037_, v_v_1038_, v_p_1039_);
return v___x_1040_;
}
}
else
{
lean_dec(v_h__3_1031_);
lean_dec(v_h__2_1030_);
if (lean_obj_tag(v_p_u2082_1028_) == 0)
{
lean_object* v_k_1041_; lean_object* v_v_1042_; lean_object* v_p_1043_; lean_object* v_k_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__4_1032_);
v_k_1041_ = lean_ctor_get(v_p_u2081_1027_, 0);
lean_inc(v_k_1041_);
v_v_1042_ = lean_ctor_get(v_p_u2081_1027_, 1);
lean_inc(v_v_1042_);
v_p_1043_ = lean_ctor_get(v_p_u2081_1027_, 2);
lean_inc_ref(v_p_1043_);
lean_dec_ref_known(v_p_u2081_1027_, 3);
v_k_1044_ = lean_ctor_get(v_p_u2082_1028_, 0);
lean_inc(v_k_1044_);
lean_dec_ref_known(v_p_u2082_1028_, 1);
v___x_1045_ = lean_apply_4(v_h__1_1029_, v_k_1041_, v_v_1042_, v_p_1043_, v_k_1044_);
return v___x_1045_;
}
else
{
lean_object* v_k_1046_; lean_object* v_v_1047_; lean_object* v_p_1048_; lean_object* v_k_1049_; lean_object* v_v_1050_; lean_object* v_p_1051_; lean_object* v___x_1052_; 
lean_dec(v_h__1_1029_);
v_k_1046_ = lean_ctor_get(v_p_u2081_1027_, 0);
lean_inc(v_k_1046_);
v_v_1047_ = lean_ctor_get(v_p_u2081_1027_, 1);
lean_inc(v_v_1047_);
v_p_1048_ = lean_ctor_get(v_p_u2081_1027_, 2);
lean_inc_ref(v_p_1048_);
lean_dec_ref_known(v_p_u2081_1027_, 3);
v_k_1049_ = lean_ctor_get(v_p_u2082_1028_, 0);
lean_inc(v_k_1049_);
v_v_1050_ = lean_ctor_get(v_p_u2082_1028_, 1);
lean_inc(v_v_1050_);
v_p_1051_ = lean_ctor_get(v_p_u2082_1028_, 2);
lean_inc_ref(v_p_1051_);
lean_dec_ref_known(v_p_u2082_1028_, 3);
v___x_1052_ = lean_apply_6(v_h__4_1032_, v_k_1046_, v_v_1047_, v_p_1048_, v_k_1049_, v_v_1050_, v_p_1051_);
return v___x_1052_;
}
}
}
}
uint8_t l_Int_Internal_Linear_not__le__of__le__cert(lean_object* v_p_u2081_1053_, lean_object* v_p_u2082_1054_){
_start:
{
if (lean_obj_tag(v_p_u2081_1053_) == 0)
{
if (lean_obj_tag(v_p_u2082_1054_) == 0)
{
lean_object* v_k_1055_; lean_object* v_k_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_k_1055_ = lean_ctor_get(v_p_u2081_1053_, 0);
v_k_1056_ = lean_ctor_get(v_p_u2082_1054_, 0);
v___x_1057_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_1058_ = lean_int_sub(v___x_1057_, v_k_1056_);
v___x_1059_ = lean_int_dec_le(v___x_1058_, v_k_1055_);
lean_dec(v___x_1058_);
return v___x_1059_;
}
else
{
uint8_t v___x_1060_; 
v___x_1060_ = 0;
return v___x_1060_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1054_) == 0)
{
uint8_t v___x_1061_; 
v___x_1061_ = 0;
return v___x_1061_;
}
else
{
lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v_p_1064_; lean_object* v_k_1065_; lean_object* v_v_1066_; lean_object* v_p_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_k_1062_ = lean_ctor_get(v_p_u2081_1053_, 0);
v_v_1063_ = lean_ctor_get(v_p_u2081_1053_, 1);
v_p_1064_ = lean_ctor_get(v_p_u2081_1053_, 2);
v_k_1065_ = lean_ctor_get(v_p_u2082_1054_, 0);
v_v_1066_ = lean_ctor_get(v_p_u2082_1054_, 1);
v_p_1067_ = lean_ctor_get(v_p_u2082_1054_, 2);
v___x_1068_ = lean_int_neg(v_k_1065_);
v___x_1069_ = lean_int_dec_eq(v_k_1062_, v___x_1068_);
lean_dec(v___x_1068_);
if (v___x_1069_ == 0)
{
return v___x_1069_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_eq(v_v_1063_, v_v_1066_);
if (v___x_1070_ == 0)
{
return v___x_1070_;
}
else
{
v_p_u2081_1053_ = v_p_1064_;
v_p_u2082_1054_ = v_p_1067_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_not__le__of__le__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1053_ = stack[0].m_obj;
lean_object* v_p_u2082_1054_ = stack[1].m_obj;
uint8_t v_res_1072_;
v_res_1072_ = l_Int_Internal_Linear_not__le__of__le__cert(v_p_u2081_1053_, v_p_u2082_1054_);
stack->m_num = v_res_1072_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_not__le__of__le__cert___boxed(lean_object* v_p_u2081_1073_, lean_object* v_p_u2082_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Int_Internal_Linear_not__le__of__le__cert(v_p_u2081_1073_, v_p_u2082_1074_);
lean_dec_ref(v_p_u2082_1074_);
lean_dec_ref(v_p_u2081_1073_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
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
