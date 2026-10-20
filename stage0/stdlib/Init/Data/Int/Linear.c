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
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* v_x_723_, lean_object* v_h__1_724_, lean_object* v_h__2_725_, lean_object* v_h__3_726_, lean_object* v_h__4_727_, lean_object* v_h__5_728_, lean_object* v_h__6_729_, lean_object* v_h__7_730_){
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
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
v_v_731_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_v_731_);
lean_dec_ref_known(v_x_723_, 1);
v___x_732_ = lean_apply_1(v_h__1_724_, v_v_731_);
return v___x_732_;
}
case 1:
{
lean_object* v_i_733_; lean_object* v___x_734_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__1_724_);
v_i_733_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_i_733_);
lean_dec_ref_known(v_x_723_, 1);
v___x_734_ = lean_apply_1(v_h__2_725_, v_i_733_);
return v___x_734_;
}
case 2:
{
lean_object* v_a_735_; lean_object* v_b_736_; lean_object* v___x_737_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_a_735_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_735_);
v_b_736_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_b_736_);
lean_dec_ref_known(v_x_723_, 2);
v___x_737_ = lean_apply_2(v_h__3_726_, v_a_735_, v_b_736_);
return v___x_737_;
}
case 3:
{
lean_object* v_a_738_; lean_object* v_b_739_; lean_object* v___x_740_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_a_738_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_738_);
v_b_739_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_b_739_);
lean_dec_ref_known(v_x_723_, 2);
v___x_740_ = lean_apply_2(v_h__4_727_, v_a_738_, v_b_739_);
return v___x_740_;
}
case 4:
{
lean_object* v_a_741_; lean_object* v___x_742_; 
lean_dec(v_h__6_729_);
lean_dec(v_h__5_728_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_a_741_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_a_741_);
lean_dec_ref_known(v_x_723_, 1);
v___x_742_ = lean_apply_1(v_h__7_730_, v_a_741_);
return v___x_742_;
}
case 5:
{
lean_object* v_k_743_; lean_object* v_a_744_; lean_object* v___x_745_; 
lean_dec(v_h__7_730_);
lean_dec(v_h__6_729_);
lean_dec(v_h__4_727_);
lean_dec(v_h__3_726_);
lean_dec(v_h__2_725_);
lean_dec(v_h__1_724_);
v_k_743_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_k_743_);
v_a_744_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_a_744_);
lean_dec_ref_known(v_x_723_, 2);
v___x_745_ = lean_apply_2(v_h__5_728_, v_k_743_, v_a_744_);
return v___x_745_;
}
default: 
{
lean_object* v_a_746_; lean_object* v_k_747_; lean_object* v___x_748_; 
lean_dec(v_h__7_730_);
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
v___x_748_ = lean_apply_2(v_h__6_729_, v_a_746_, v_k_747_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* v_motive_749_, lean_object* v_x_750_, lean_object* v_h__1_751_, lean_object* v_h__2_752_, lean_object* v_h__3_753_, lean_object* v_h__4_754_, lean_object* v_h__5_755_, lean_object* v_h__6_756_, lean_object* v_h__7_757_){
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
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
v_v_758_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_v_758_);
lean_dec_ref_known(v_x_750_, 1);
v___x_759_ = lean_apply_1(v_h__1_751_, v_v_758_);
return v___x_759_;
}
case 1:
{
lean_object* v_i_760_; lean_object* v___x_761_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__1_751_);
v_i_760_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_i_760_);
lean_dec_ref_known(v_x_750_, 1);
v___x_761_ = lean_apply_1(v_h__2_752_, v_i_760_);
return v___x_761_;
}
case 2:
{
lean_object* v_a_762_; lean_object* v_b_763_; lean_object* v___x_764_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_a_762_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_762_);
v_b_763_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_b_763_);
lean_dec_ref_known(v_x_750_, 2);
v___x_764_ = lean_apply_2(v_h__3_753_, v_a_762_, v_b_763_);
return v___x_764_;
}
case 3:
{
lean_object* v_a_765_; lean_object* v_b_766_; lean_object* v___x_767_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_a_765_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_765_);
v_b_766_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_b_766_);
lean_dec_ref_known(v_x_750_, 2);
v___x_767_ = lean_apply_2(v_h__4_754_, v_a_765_, v_b_766_);
return v___x_767_;
}
case 4:
{
lean_object* v_a_768_; lean_object* v___x_769_; 
lean_dec(v_h__6_756_);
lean_dec(v_h__5_755_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_a_768_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_a_768_);
lean_dec_ref_known(v_x_750_, 1);
v___x_769_ = lean_apply_1(v_h__7_757_, v_a_768_);
return v___x_769_;
}
case 5:
{
lean_object* v_k_770_; lean_object* v_a_771_; lean_object* v___x_772_; 
lean_dec(v_h__7_757_);
lean_dec(v_h__6_756_);
lean_dec(v_h__4_754_);
lean_dec(v_h__3_753_);
lean_dec(v_h__2_752_);
lean_dec(v_h__1_751_);
v_k_770_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_k_770_);
v_a_771_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_a_771_);
lean_dec_ref_known(v_x_750_, 2);
v___x_772_ = lean_apply_2(v_h__5_755_, v_k_770_, v_a_771_);
return v___x_772_;
}
default: 
{
lean_object* v_a_773_; lean_object* v_k_774_; lean_object* v___x_775_; 
lean_dec(v_h__7_757_);
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
v___x_775_ = lean_apply_2(v_h__6_756_, v_a_773_, v_k_774_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object* v_p_776_){
_start:
{
if (lean_obj_tag(v_p_776_) == 0)
{
lean_object* v_k_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_k_777_ = lean_ctor_get(v_p_776_, 0);
v___x_778_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_779_ = lean_int_dec_eq(v_k_777_, v___x_778_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
else
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatEq___boxed(lean_object* v_p_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Int_Internal_Linear_Poly_isUnsatEq(v_p_783_);
lean_dec_ref(v_p_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object* v_p_786_){
_start:
{
if (lean_obj_tag(v_p_786_) == 0)
{
lean_object* v_k_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_k_787_ = lean_ctor_get(v_p_786_, 0);
v___x_788_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_789_ = lean_int_dec_eq(v_k_787_, v___x_788_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = 0;
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidEq___boxed(lean_object* v_p_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Int_Internal_Linear_Poly_isValidEq(v_p_791_);
lean_dec_ref(v_p_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* v_p_794_, lean_object* v_h__1_795_, lean_object* v_h__2_796_){
_start:
{
if (lean_obj_tag(v_p_794_) == 0)
{
lean_object* v_k_797_; lean_object* v___x_798_; 
lean_dec(v_h__2_796_);
v_k_797_ = lean_ctor_get(v_p_794_, 0);
lean_inc(v_k_797_);
lean_dec_ref_known(v_p_794_, 1);
v___x_798_ = lean_apply_1(v_h__1_795_, v_k_797_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; 
lean_dec(v_h__1_795_);
v___x_799_ = lean_apply_2(v_h__2_796_, v_p_794_, lean_box(0));
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* v_motive_800_, lean_object* v_p_801_, lean_object* v_h__1_802_, lean_object* v_h__2_803_){
_start:
{
if (lean_obj_tag(v_p_801_) == 0)
{
lean_object* v_k_804_; lean_object* v___x_805_; 
lean_dec(v_h__2_803_);
v_k_804_ = lean_ctor_get(v_p_801_, 0);
lean_inc(v_k_804_);
lean_dec_ref_known(v_p_801_, 1);
v___x_805_ = lean_apply_1(v_h__1_802_, v_k_804_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; 
lean_dec(v_h__1_802_);
v___x_806_ = lean_apply_2(v_h__2_803_, v_p_801_, lean_box(0));
return v___x_806_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object* v_p_807_){
_start:
{
if (lean_obj_tag(v_p_807_) == 0)
{
lean_object* v_k_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_k_808_ = lean_ctor_get(v_p_807_, 0);
v___x_809_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_810_ = lean_int_dec_lt(v___x_809_, v_k_808_);
return v___x_810_;
}
else
{
uint8_t v___x_811_; 
v___x_811_ = 0;
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatLe___boxed(lean_object* v_p_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_812_);
lean_dec_ref(v_p_812_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object* v_p_815_){
_start:
{
if (lean_obj_tag(v_p_815_) == 0)
{
lean_object* v_k_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_k_816_ = lean_ctor_get(v_p_815_, 0);
v___x_817_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_818_ = lean_int_dec_le(v_k_816_, v___x_817_);
return v___x_818_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidLe___boxed(lean_object* v_p_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Int_Internal_Linear_Poly_isValidLe(v_p_820_);
lean_dec_ref(v_p_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(lean_object* v_a_823_, lean_object* v_b_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = l_Int_gcd(v_a_823_, v_b_824_);
v___x_826_ = lean_nat_to_int(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd___boxed(lean_object* v_a_827_, lean_object* v_b_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(v_a_827_, v_b_828_);
lean_dec(v_b_828_);
lean_dec(v_a_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
return v_x_831_;
}
else
{
lean_object* v_k_832_; lean_object* v_p_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_k_832_ = lean_ctor_get(v_x_830_, 0);
v_p_833_ = lean_ctor_get(v_x_830_, 2);
v___x_834_ = l_Int_gcd(v_k_832_, v_x_831_);
lean_dec(v_x_831_);
v___x_835_ = lean_nat_to_int(v___x_834_);
v_x_830_ = v_p_833_;
v_x_831_ = v___x_835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs___boxed(lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_x_837_, v_x_838_);
lean_dec_ref(v_x_837_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object* v_k_840_, lean_object* v_p_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_842_ = l_Int_Internal_Linear_Poly_getConst(v_p_841_);
v___x_843_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_841_, v_k_840_);
v___x_844_ = lean_int_emod(v___x_842_, v___x_843_);
lean_dec(v___x_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_846_ = lean_int_dec_eq(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
v___x_847_ = 1;
return v___x_847_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDvd___boxed(lean_object* v_k_849_, lean_object* v_p_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_k_849_, v_p_850_);
lean_dec_ref(v_p_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object* v_p_u2081_853_, lean_object* v_p_u2082_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_){
_start:
{
if (lean_obj_tag(v_p_u2081_853_) == 1)
{
if (lean_obj_tag(v_p_u2082_854_) == 1)
{
lean_object* v_k_857_; lean_object* v_v_858_; lean_object* v_p_859_; lean_object* v_k_860_; lean_object* v_v_861_; lean_object* v_p_862_; lean_object* v___x_863_; 
lean_dec(v_h__2_856_);
v_k_857_ = lean_ctor_get(v_p_u2081_853_, 0);
lean_inc(v_k_857_);
v_v_858_ = lean_ctor_get(v_p_u2081_853_, 1);
lean_inc(v_v_858_);
v_p_859_ = lean_ctor_get(v_p_u2081_853_, 2);
lean_inc_ref(v_p_859_);
lean_dec_ref_known(v_p_u2081_853_, 3);
v_k_860_ = lean_ctor_get(v_p_u2082_854_, 0);
lean_inc(v_k_860_);
v_v_861_ = lean_ctor_get(v_p_u2082_854_, 1);
lean_inc(v_v_861_);
v_p_862_ = lean_ctor_get(v_p_u2082_854_, 2);
lean_inc_ref(v_p_862_);
lean_dec_ref_known(v_p_u2082_854_, 3);
v___x_863_ = lean_apply_6(v_h__1_855_, v_k_857_, v_v_858_, v_p_859_, v_k_860_, v_v_861_, v_p_862_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; 
lean_dec(v_h__1_855_);
v___x_864_ = lean_apply_3(v_h__2_856_, v_p_u2081_853_, v_p_u2082_854_, lean_box(0));
return v___x_864_;
}
}
else
{
lean_object* v___x_865_; 
lean_dec(v_h__1_855_);
v___x_865_ = lean_apply_3(v_h__2_856_, v_p_u2081_853_, v_p_u2082_854_, lean_box(0));
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object* v_motive_866_, lean_object* v_p_u2081_867_, lean_object* v_p_u2082_868_, lean_object* v_h__1_869_, lean_object* v_h__2_870_){
_start:
{
if (lean_obj_tag(v_p_u2081_867_) == 1)
{
if (lean_obj_tag(v_p_u2082_868_) == 1)
{
lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_p_873_; lean_object* v_k_874_; lean_object* v_v_875_; lean_object* v_p_876_; lean_object* v___x_877_; 
lean_dec(v_h__2_870_);
v_k_871_ = lean_ctor_get(v_p_u2081_867_, 0);
lean_inc(v_k_871_);
v_v_872_ = lean_ctor_get(v_p_u2081_867_, 1);
lean_inc(v_v_872_);
v_p_873_ = lean_ctor_get(v_p_u2081_867_, 2);
lean_inc_ref(v_p_873_);
lean_dec_ref_known(v_p_u2081_867_, 3);
v_k_874_ = lean_ctor_get(v_p_u2082_868_, 0);
lean_inc(v_k_874_);
v_v_875_ = lean_ctor_get(v_p_u2082_868_, 1);
lean_inc(v_v_875_);
v_p_876_ = lean_ctor_get(v_p_u2082_868_, 2);
lean_inc_ref(v_p_876_);
lean_dec_ref_known(v_p_u2082_868_, 3);
v___x_877_ = lean_apply_6(v_h__1_869_, v_k_871_, v_v_872_, v_p_873_, v_k_874_, v_v_875_, v_p_876_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; 
lean_dec(v_h__1_869_);
v___x_878_ = lean_apply_3(v_h__2_870_, v_p_u2081_867_, v_p_u2082_868_, lean_box(0));
return v___x_878_;
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v_h__1_869_);
v___x_879_ = lean_apply_3(v_h__2_870_, v_p_u2081_867_, v_p_u2082_868_, lean_box(0));
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object* v_p_880_){
_start:
{
if (lean_obj_tag(v_p_880_) == 1)
{
lean_object* v_k_881_; 
v_k_881_ = lean_ctor_get(v_p_880_, 0);
lean_inc(v_k_881_);
return v_k_881_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff___boxed(lean_object* v_p_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_883_);
lean_dec_ref(v_p_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object* v_p_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_p_885_) == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
return v___x_887_;
}
else
{
lean_object* v_k_888_; lean_object* v_v_889_; lean_object* v_p_890_; uint8_t v___x_891_; 
v_k_888_ = lean_ctor_get(v_p_885_, 0);
v_v_889_ = lean_ctor_get(v_p_885_, 1);
v_p_890_ = lean_ctor_get(v_p_885_, 2);
v___x_891_ = lean_nat_dec_eq(v_x_886_, v_v_889_);
if (v___x_891_ == 0)
{
v_p_885_ = v_p_890_;
goto _start;
}
else
{
lean_inc(v_k_888_);
return v_k_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff___boxed(lean_object* v_p_893_, lean_object* v_x_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Int_Internal_Linear_Poly_coeff(v_p_893_, v_x_894_);
lean_dec(v_x_894_);
lean_dec_ref(v_p_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs(lean_object* v_x_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_nat_abs(v_x_896_);
v___x_898_ = lean_nat_to_int(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs___boxed(lean_object* v_x_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Int_Internal_Linear_abs(v_x_899_);
lean_dec(v_x_899_);
return v_res_900_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDiseq(lean_object* v_p_901_){
_start:
{
if (lean_obj_tag(v_p_901_) == 0)
{
lean_object* v_k_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_k_902_ = lean_ctor_get(v_p_901_, 0);
v___x_903_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_904_ = lean_int_dec_eq(v_k_902_, v___x_903_);
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = 0;
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDiseq___boxed(lean_object* v_p_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l_Int_Internal_Linear_Poly_isUnsatDiseq(v_p_906_);
lean_dec_ref(v_p_906_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail(lean_object* v_p_909_){
_start:
{
if (lean_obj_tag(v_p_909_) == 1)
{
lean_object* v_p_910_; 
v_p_910_ = lean_ctor_get(v_p_909_, 2);
lean_inc_ref(v_p_910_);
return v_p_910_;
}
else
{
lean_inc_ref(v_p_909_);
return v_p_909_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail___boxed(lean_object* v_p_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Int_Internal_Linear_Poly_tail(v_p_911_);
lean_dec_ref(v_p_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object* v_p_913_, lean_object* v_h__1_914_, lean_object* v_h__2_915_){
_start:
{
if (lean_obj_tag(v_p_913_) == 1)
{
lean_object* v_k_916_; lean_object* v_v_917_; lean_object* v_p_918_; lean_object* v___x_919_; 
lean_dec(v_h__2_915_);
v_k_916_ = lean_ctor_get(v_p_913_, 0);
lean_inc(v_k_916_);
v_v_917_ = lean_ctor_get(v_p_913_, 1);
lean_inc(v_v_917_);
v_p_918_ = lean_ctor_get(v_p_913_, 2);
lean_inc_ref(v_p_918_);
lean_dec_ref_known(v_p_913_, 3);
v___x_919_ = lean_apply_3(v_h__1_914_, v_k_916_, v_v_917_, v_p_918_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; 
lean_dec(v_h__1_914_);
v___x_920_ = lean_apply_2(v_h__2_915_, v_p_913_, lean_box(0));
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter(lean_object* v_motive_921_, lean_object* v_p_922_, lean_object* v_h__1_923_, lean_object* v_h__2_924_){
_start:
{
if (lean_obj_tag(v_p_922_) == 1)
{
lean_object* v_k_925_; lean_object* v_v_926_; lean_object* v_p_927_; lean_object* v___x_928_; 
lean_dec(v_h__2_924_);
v_k_925_ = lean_ctor_get(v_p_922_, 0);
lean_inc(v_k_925_);
v_v_926_ = lean_ctor_get(v_p_922_, 1);
lean_inc(v_v_926_);
v_p_927_ = lean_ctor_get(v_p_922_, 2);
lean_inc_ref(v_p_927_);
lean_dec_ref_known(v_p_922_, 3);
v___x_928_ = lean_apply_3(v_h__1_923_, v_k_925_, v_v_926_, v_p_927_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; 
lean_dec(v_h__1_923_);
v___x_929_ = lean_apply_2(v_h__2_924_, v_p_922_, lean_box(0));
return v___x_929_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnAdd(lean_object* v_p_930_, lean_object* v_k_931_){
_start:
{
if (lean_obj_tag(v_p_930_) == 0)
{
uint8_t v___x_932_; 
lean_dec_ref_known(v_p_930_, 1);
lean_dec_ref(v_k_931_);
v___x_932_ = 0;
return v___x_932_;
}
else
{
lean_object* v_a_933_; lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_a_933_ = lean_ctor_get(v_p_930_, 0);
lean_inc(v_a_933_);
v_a_934_ = lean_ctor_get(v_p_930_, 1);
lean_inc(v_a_934_);
v_a_935_ = lean_ctor_get(v_p_930_, 2);
lean_inc_ref(v_a_935_);
lean_dec_ref_known(v_p_930_, 3);
v___x_936_ = lean_apply_3(v_k_931_, v_a_933_, v_a_934_, v_a_935_);
v___x_937_ = lean_unbox(v___x_936_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnAdd___boxed(lean_object* v_p_938_, lean_object* v_k_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Int_Internal_Linear_Poly_casesOnAdd(v_p_938_, v_k_939_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnNum(lean_object* v_p_942_, lean_object* v_k_943_){
_start:
{
if (lean_obj_tag(v_p_942_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_a_944_ = lean_ctor_get(v_p_942_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v_p_942_, 1);
v___x_945_ = lean_apply_1(v_k_943_, v_a_944_);
v___x_946_ = lean_unbox(v___x_945_);
return v___x_946_;
}
else
{
uint8_t v___x_947_; 
lean_dec_ref_known(v_p_942_, 3);
lean_dec_ref(v_k_943_);
v___x_947_ = 0;
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnNum___boxed(lean_object* v_p_948_, lean_object* v_k_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Int_Internal_Linear_Poly_casesOnNum(v_p_948_, v_k_949_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_emod__le__cert(lean_object* v_y_952_, lean_object* v_n_953_){
_start:
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_955_ = lean_int_dec_eq(v_y_952_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_956_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_957_ = lean_nat_abs(v_y_952_);
v___x_958_ = lean_nat_to_int(v___x_957_);
v___x_959_ = lean_int_sub(v___x_956_, v___x_958_);
lean_dec(v___x_958_);
v___x_960_ = lean_int_dec_eq(v_n_953_, v___x_959_);
lean_dec(v___x_959_);
return v___x_960_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = 0;
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_emod__le__cert___boxed(lean_object* v_y_962_, lean_object* v_n_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l_Int_Internal_Linear_emod__le__cert(v_y_962_, v_n_963_);
lean_dec(v_n_963_);
lean_dec(v_y_962_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_le__of__le__cert(lean_object* v_p_u2081_966_, lean_object* v_p_u2082_967_){
_start:
{
if (lean_obj_tag(v_p_u2081_966_) == 0)
{
if (lean_obj_tag(v_p_u2082_967_) == 0)
{
lean_object* v_k_968_; lean_object* v_k_969_; uint8_t v___x_970_; 
v_k_968_ = lean_ctor_get(v_p_u2081_966_, 0);
v_k_969_ = lean_ctor_get(v_p_u2082_967_, 0);
v___x_970_ = lean_int_dec_le(v_k_969_, v_k_968_);
return v___x_970_;
}
else
{
uint8_t v___x_971_; 
v___x_971_ = 0;
return v___x_971_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_967_) == 0)
{
uint8_t v___x_972_; 
v___x_972_ = 0;
return v___x_972_;
}
else
{
lean_object* v_k_973_; lean_object* v_v_974_; lean_object* v_p_975_; lean_object* v_k_976_; lean_object* v_v_977_; lean_object* v_p_978_; uint8_t v___x_979_; 
v_k_973_ = lean_ctor_get(v_p_u2081_966_, 0);
v_v_974_ = lean_ctor_get(v_p_u2081_966_, 1);
v_p_975_ = lean_ctor_get(v_p_u2081_966_, 2);
v_k_976_ = lean_ctor_get(v_p_u2082_967_, 0);
v_v_977_ = lean_ctor_get(v_p_u2082_967_, 1);
v_p_978_ = lean_ctor_get(v_p_u2082_967_, 2);
v___x_979_ = lean_int_dec_eq(v_k_973_, v_k_976_);
if (v___x_979_ == 0)
{
return v___x_979_;
}
else
{
uint8_t v___x_980_; 
v___x_980_ = lean_nat_dec_eq(v_v_974_, v_v_977_);
if (v___x_980_ == 0)
{
return v___x_980_;
}
else
{
v_p_u2081_966_ = v_p_975_;
v_p_u2082_967_ = v_p_978_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_le__of__le__cert___boxed(lean_object* v_p_u2081_982_, lean_object* v_p_u2082_983_){
_start:
{
uint8_t v_res_984_; lean_object* v_r_985_; 
v_res_984_ = l_Int_Internal_Linear_le__of__le__cert(v_p_u2081_982_, v_p_u2082_983_);
lean_dec_ref(v_p_u2082_983_);
lean_dec_ref(v_p_u2081_982_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object* v_p_u2081_986_, lean_object* v_p_u2082_987_, lean_object* v_h__1_988_, lean_object* v_h__2_989_, lean_object* v_h__3_990_, lean_object* v_h__4_991_){
_start:
{
if (lean_obj_tag(v_p_u2081_986_) == 0)
{
lean_dec(v_h__4_991_);
lean_dec(v_h__1_988_);
if (lean_obj_tag(v_p_u2082_987_) == 0)
{
lean_object* v_k_992_; lean_object* v_k_993_; lean_object* v___x_994_; 
lean_dec(v_h__2_989_);
v_k_992_ = lean_ctor_get(v_p_u2081_986_, 0);
lean_inc(v_k_992_);
lean_dec_ref_known(v_p_u2081_986_, 1);
v_k_993_ = lean_ctor_get(v_p_u2082_987_, 0);
lean_inc(v_k_993_);
lean_dec_ref_known(v_p_u2082_987_, 1);
v___x_994_ = lean_apply_2(v_h__3_990_, v_k_992_, v_k_993_);
return v___x_994_;
}
else
{
lean_object* v_k_995_; lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v_p_998_; lean_object* v___x_999_; 
lean_dec(v_h__3_990_);
v_k_995_ = lean_ctor_get(v_p_u2081_986_, 0);
lean_inc(v_k_995_);
lean_dec_ref_known(v_p_u2081_986_, 1);
v_k_996_ = lean_ctor_get(v_p_u2082_987_, 0);
lean_inc(v_k_996_);
v_v_997_ = lean_ctor_get(v_p_u2082_987_, 1);
lean_inc(v_v_997_);
v_p_998_ = lean_ctor_get(v_p_u2082_987_, 2);
lean_inc_ref(v_p_998_);
lean_dec_ref_known(v_p_u2082_987_, 3);
v___x_999_ = lean_apply_4(v_h__2_989_, v_k_995_, v_k_996_, v_v_997_, v_p_998_);
return v___x_999_;
}
}
else
{
lean_dec(v_h__3_990_);
lean_dec(v_h__2_989_);
if (lean_obj_tag(v_p_u2082_987_) == 0)
{
lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v_p_1002_; lean_object* v_k_1003_; lean_object* v___x_1004_; 
lean_dec(v_h__4_991_);
v_k_1000_ = lean_ctor_get(v_p_u2081_986_, 0);
lean_inc(v_k_1000_);
v_v_1001_ = lean_ctor_get(v_p_u2081_986_, 1);
lean_inc(v_v_1001_);
v_p_1002_ = lean_ctor_get(v_p_u2081_986_, 2);
lean_inc_ref(v_p_1002_);
lean_dec_ref_known(v_p_u2081_986_, 3);
v_k_1003_ = lean_ctor_get(v_p_u2082_987_, 0);
lean_inc(v_k_1003_);
lean_dec_ref_known(v_p_u2082_987_, 1);
v___x_1004_ = lean_apply_4(v_h__1_988_, v_k_1000_, v_v_1001_, v_p_1002_, v_k_1003_);
return v___x_1004_;
}
else
{
lean_object* v_k_1005_; lean_object* v_v_1006_; lean_object* v_p_1007_; lean_object* v_k_1008_; lean_object* v_v_1009_; lean_object* v_p_1010_; lean_object* v___x_1011_; 
lean_dec(v_h__1_988_);
v_k_1005_ = lean_ctor_get(v_p_u2081_986_, 0);
lean_inc(v_k_1005_);
v_v_1006_ = lean_ctor_get(v_p_u2081_986_, 1);
lean_inc(v_v_1006_);
v_p_1007_ = lean_ctor_get(v_p_u2081_986_, 2);
lean_inc_ref(v_p_1007_);
lean_dec_ref_known(v_p_u2081_986_, 3);
v_k_1008_ = lean_ctor_get(v_p_u2082_987_, 0);
lean_inc(v_k_1008_);
v_v_1009_ = lean_ctor_get(v_p_u2082_987_, 1);
lean_inc(v_v_1009_);
v_p_1010_ = lean_ctor_get(v_p_u2082_987_, 2);
lean_inc_ref(v_p_1010_);
lean_dec_ref_known(v_p_u2082_987_, 3);
v___x_1011_ = lean_apply_6(v_h__4_991_, v_k_1005_, v_v_1006_, v_p_1007_, v_k_1008_, v_v_1009_, v_p_1010_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_le__of__le__cert_match__1_splitter(lean_object* v_motive_1012_, lean_object* v_p_u2081_1013_, lean_object* v_p_u2082_1014_, lean_object* v_h__1_1015_, lean_object* v_h__2_1016_, lean_object* v_h__3_1017_, lean_object* v_h__4_1018_){
_start:
{
if (lean_obj_tag(v_p_u2081_1013_) == 0)
{
lean_dec(v_h__4_1018_);
lean_dec(v_h__1_1015_);
if (lean_obj_tag(v_p_u2082_1014_) == 0)
{
lean_object* v_k_1019_; lean_object* v_k_1020_; lean_object* v___x_1021_; 
lean_dec(v_h__2_1016_);
v_k_1019_ = lean_ctor_get(v_p_u2081_1013_, 0);
lean_inc(v_k_1019_);
lean_dec_ref_known(v_p_u2081_1013_, 1);
v_k_1020_ = lean_ctor_get(v_p_u2082_1014_, 0);
lean_inc(v_k_1020_);
lean_dec_ref_known(v_p_u2082_1014_, 1);
v___x_1021_ = lean_apply_2(v_h__3_1017_, v_k_1019_, v_k_1020_);
return v___x_1021_;
}
else
{
lean_object* v_k_1022_; lean_object* v_k_1023_; lean_object* v_v_1024_; lean_object* v_p_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__3_1017_);
v_k_1022_ = lean_ctor_get(v_p_u2081_1013_, 0);
lean_inc(v_k_1022_);
lean_dec_ref_known(v_p_u2081_1013_, 1);
v_k_1023_ = lean_ctor_get(v_p_u2082_1014_, 0);
lean_inc(v_k_1023_);
v_v_1024_ = lean_ctor_get(v_p_u2082_1014_, 1);
lean_inc(v_v_1024_);
v_p_1025_ = lean_ctor_get(v_p_u2082_1014_, 2);
lean_inc_ref(v_p_1025_);
lean_dec_ref_known(v_p_u2082_1014_, 3);
v___x_1026_ = lean_apply_4(v_h__2_1016_, v_k_1022_, v_k_1023_, v_v_1024_, v_p_1025_);
return v___x_1026_;
}
}
else
{
lean_dec(v_h__3_1017_);
lean_dec(v_h__2_1016_);
if (lean_obj_tag(v_p_u2082_1014_) == 0)
{
lean_object* v_k_1027_; lean_object* v_v_1028_; lean_object* v_p_1029_; lean_object* v_k_1030_; lean_object* v___x_1031_; 
lean_dec(v_h__4_1018_);
v_k_1027_ = lean_ctor_get(v_p_u2081_1013_, 0);
lean_inc(v_k_1027_);
v_v_1028_ = lean_ctor_get(v_p_u2081_1013_, 1);
lean_inc(v_v_1028_);
v_p_1029_ = lean_ctor_get(v_p_u2081_1013_, 2);
lean_inc_ref(v_p_1029_);
lean_dec_ref_known(v_p_u2081_1013_, 3);
v_k_1030_ = lean_ctor_get(v_p_u2082_1014_, 0);
lean_inc(v_k_1030_);
lean_dec_ref_known(v_p_u2082_1014_, 1);
v___x_1031_ = lean_apply_4(v_h__1_1015_, v_k_1027_, v_v_1028_, v_p_1029_, v_k_1030_);
return v___x_1031_;
}
else
{
lean_object* v_k_1032_; lean_object* v_v_1033_; lean_object* v_p_1034_; lean_object* v_k_1035_; lean_object* v_v_1036_; lean_object* v_p_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__1_1015_);
v_k_1032_ = lean_ctor_get(v_p_u2081_1013_, 0);
lean_inc(v_k_1032_);
v_v_1033_ = lean_ctor_get(v_p_u2081_1013_, 1);
lean_inc(v_v_1033_);
v_p_1034_ = lean_ctor_get(v_p_u2081_1013_, 2);
lean_inc_ref(v_p_1034_);
lean_dec_ref_known(v_p_u2081_1013_, 3);
v_k_1035_ = lean_ctor_get(v_p_u2082_1014_, 0);
lean_inc(v_k_1035_);
v_v_1036_ = lean_ctor_get(v_p_u2082_1014_, 1);
lean_inc(v_v_1036_);
v_p_1037_ = lean_ctor_get(v_p_u2082_1014_, 2);
lean_inc_ref(v_p_1037_);
lean_dec_ref_known(v_p_u2082_1014_, 3);
v___x_1038_ = lean_apply_6(v_h__4_1018_, v_k_1032_, v_v_1033_, v_p_1034_, v_k_1035_, v_v_1036_, v_p_1037_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_not__le__of__le__cert(lean_object* v_p_u2081_1039_, lean_object* v_p_u2082_1040_){
_start:
{
if (lean_obj_tag(v_p_u2081_1039_) == 0)
{
if (lean_obj_tag(v_p_u2082_1040_) == 0)
{
lean_object* v_k_1041_; lean_object* v_k_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_k_1041_ = lean_ctor_get(v_p_u2081_1039_, 0);
v_k_1042_ = lean_ctor_get(v_p_u2082_1040_, 0);
v___x_1043_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
v___x_1044_ = lean_int_sub(v___x_1043_, v_k_1042_);
v___x_1045_ = lean_int_dec_le(v___x_1044_, v_k_1041_);
lean_dec(v___x_1044_);
return v___x_1045_;
}
else
{
uint8_t v___x_1046_; 
v___x_1046_ = 0;
return v___x_1046_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1040_) == 0)
{
uint8_t v___x_1047_; 
v___x_1047_ = 0;
return v___x_1047_;
}
else
{
lean_object* v_k_1048_; lean_object* v_v_1049_; lean_object* v_p_1050_; lean_object* v_k_1051_; lean_object* v_v_1052_; lean_object* v_p_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_k_1048_ = lean_ctor_get(v_p_u2081_1039_, 0);
v_v_1049_ = lean_ctor_get(v_p_u2081_1039_, 1);
v_p_1050_ = lean_ctor_get(v_p_u2081_1039_, 2);
v_k_1051_ = lean_ctor_get(v_p_u2082_1040_, 0);
v_v_1052_ = lean_ctor_get(v_p_u2082_1040_, 1);
v_p_1053_ = lean_ctor_get(v_p_u2082_1040_, 2);
v___x_1054_ = lean_int_neg(v_k_1051_);
v___x_1055_ = lean_int_dec_eq(v_k_1048_, v___x_1054_);
lean_dec(v___x_1054_);
if (v___x_1055_ == 0)
{
return v___x_1055_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_eq(v_v_1049_, v_v_1052_);
if (v___x_1056_ == 0)
{
return v___x_1056_;
}
else
{
v_p_u2081_1039_ = v_p_1050_;
v_p_u2082_1040_ = v_p_1053_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_not__le__of__le__cert___boxed(lean_object* v_p_u2081_1058_, lean_object* v_p_u2082_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Int_Internal_Linear_not__le__of__le__cert(v_p_u2081_1058_, v_p_u2082_1059_);
lean_dec_ref(v_p_u2082_1059_);
lean_dec_ref(v_p_u2081_1058_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
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
