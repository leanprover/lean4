// Lean compiler output
// Module: Init.Data.Int.Linear
// Imports: import all Init.Data.Int.Gcd import all Init.Data.AC import Init.LawfulBEqTactics public import Init.Data.Bool public import Init.Data.Int.Gcd public import Init.Data.RArray public import Init.Data.Int.Kernel import Init.Data.Int.Cooper import Init.Data.Int.LemmasAux
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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_bmodCoeffs(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_divCoeffs(lean_object* v_k_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
uint8_t v___x_578_; 
v___x_578_ = 1;
return v___x_578_;
}
else
{
lean_object* v_k_579_; lean_object* v_p_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_k_579_ = lean_ctor_get(v_x_577_, 0);
v_p_580_ = lean_ctor_get(v_x_577_, 2);
v___x_581_ = lean_int_emod(v_k_579_, v_k_576_);
v___x_582_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_583_ = lean_int_dec_eq(v___x_581_, v___x_582_);
lean_dec(v___x_581_);
if (v___x_583_ == 0)
{
return v___x_583_;
}
else
{
v_x_577_ = v_p_580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_divCoeffs___boxed(lean_object* v_k_585_, lean_object* v_x_586_){
_start:
{
uint8_t v_res_587_; lean_object* v_r_588_; 
v_res_587_ = l_Int_Internal_Linear_Poly_divCoeffs(v_k_585_, v_x_586_);
lean_dec_ref(v_x_586_);
lean_dec(v_k_585_);
v_r_588_ = lean_box(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27(lean_object* v_p_589_, lean_object* v_k_590_){
_start:
{
if (lean_obj_tag(v_p_589_) == 0)
{
lean_object* v_k_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_k_591_ = lean_ctor_get(v_p_589_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_p_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_p_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_k_591_);
lean_dec(v_p_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_int_mul(v_k_590_, v_k_591_);
lean_dec(v_k_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_k_600_; lean_object* v_v_601_; lean_object* v_p_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_611_; 
v_k_600_ = lean_ctor_get(v_p_589_, 0);
v_v_601_ = lean_ctor_get(v_p_589_, 1);
v_p_602_ = lean_ctor_get(v_p_589_, 2);
v_isSharedCheck_611_ = !lean_is_exclusive(v_p_589_);
if (v_isSharedCheck_611_ == 0)
{
v___x_604_ = v_p_589_;
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_p_602_);
lean_inc(v_v_601_);
lean_inc(v_k_600_);
lean_dec(v_p_589_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_int_mul(v_k_590_, v_k_600_);
lean_dec(v_k_600_);
v___x_607_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_602_, v_k_590_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v___x_607_);
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_v_601_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul_x27___boxed(lean_object* v_p_612_, lean_object* v_k_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_612_, v_k_613_);
lean_dec(v_k_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul(lean_object* v_p_615_, lean_object* v_k_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_618_ = lean_int_dec_eq(v_k_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = l_Int_Internal_Linear_Poly_mul_x27(v_p_615_, v_k_616_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v_p_615_);
v___x_620_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__1, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__1);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_mul___boxed(lean_object* v_p_621_, lean_object* v_k_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Int_Internal_Linear_Poly_mul(v_p_621_, v_k_622_);
lean_dec(v_k_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object* v_fuel_624_, lean_object* v_h__1_625_, lean_object* v_h__2_626_){
_start:
{
lean_object* v_zero_627_; uint8_t v_isZero_628_; 
v_zero_627_ = lean_unsigned_to_nat(0u);
v_isZero_628_ = lean_nat_dec_eq(v_fuel_624_, v_zero_627_);
if (v_isZero_628_ == 1)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v_h__2_626_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_apply_1(v_h__1_625_, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v_one_631_; lean_object* v_n_632_; lean_object* v___x_633_; 
lean_dec(v_h__1_625_);
v_one_631_ = lean_unsigned_to_nat(1u);
v_n_632_ = lean_nat_sub(v_fuel_624_, v_one_631_);
v___x_633_ = lean_apply_1(v_h__2_626_, v_n_632_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object* v_fuel_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___redArg(v_fuel_634_, v_h__1_635_, v_h__2_636_);
lean_dec(v_fuel_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(lean_object* v_motive_638_, lean_object* v_fuel_639_, lean_object* v_h__1_640_, lean_object* v_h__2_641_){
_start:
{
lean_object* v_zero_642_; uint8_t v_isZero_643_; 
v_zero_642_ = lean_unsigned_to_nat(0u);
v_isZero_643_ = lean_nat_dec_eq(v_fuel_639_, v_zero_642_);
if (v_isZero_643_ == 1)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_h__2_641_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_apply_1(v_h__1_640_, v___x_644_);
return v___x_645_;
}
else
{
lean_object* v_one_646_; lean_object* v_n_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_640_);
v_one_646_ = lean_unsigned_to_nat(1u);
v_n_647_ = lean_nat_sub(v_fuel_639_, v_one_646_);
v___x_648_ = lean_apply_1(v_h__2_641_, v_n_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object* v_motive_649_, lean_object* v_fuel_650_, lean_object* v_h__1_651_, lean_object* v_h__2_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__3_splitter(v_motive_649_, v_fuel_650_, v_h__1_651_, v_h__2_652_);
lean_dec(v_fuel_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object* v_p_u2081_654_, lean_object* v_p_u2082_655_, lean_object* v_h__1_656_, lean_object* v_h__2_657_, lean_object* v_h__3_658_, lean_object* v_h__4_659_){
_start:
{
if (lean_obj_tag(v_p_u2081_654_) == 0)
{
lean_dec(v_h__4_659_);
lean_dec(v_h__3_658_);
if (lean_obj_tag(v_p_u2082_655_) == 0)
{
lean_object* v_k_660_; lean_object* v_k_661_; lean_object* v___x_662_; 
lean_dec(v_h__2_657_);
v_k_660_ = lean_ctor_get(v_p_u2081_654_, 0);
lean_inc(v_k_660_);
lean_dec_ref_known(v_p_u2081_654_, 1);
v_k_661_ = lean_ctor_get(v_p_u2082_655_, 0);
lean_inc(v_k_661_);
lean_dec_ref_known(v_p_u2082_655_, 1);
v___x_662_ = lean_apply_2(v_h__1_656_, v_k_660_, v_k_661_);
return v___x_662_;
}
else
{
lean_object* v_k_663_; lean_object* v_k_664_; lean_object* v_v_665_; lean_object* v_p_666_; lean_object* v___x_667_; 
lean_dec(v_h__1_656_);
v_k_663_ = lean_ctor_get(v_p_u2081_654_, 0);
lean_inc(v_k_663_);
lean_dec_ref_known(v_p_u2081_654_, 1);
v_k_664_ = lean_ctor_get(v_p_u2082_655_, 0);
lean_inc(v_k_664_);
v_v_665_ = lean_ctor_get(v_p_u2082_655_, 1);
lean_inc(v_v_665_);
v_p_666_ = lean_ctor_get(v_p_u2082_655_, 2);
lean_inc_ref(v_p_666_);
lean_dec_ref_known(v_p_u2082_655_, 3);
v___x_667_ = lean_apply_4(v_h__2_657_, v_k_663_, v_k_664_, v_v_665_, v_p_666_);
return v___x_667_;
}
}
else
{
lean_dec(v_h__2_657_);
lean_dec(v_h__1_656_);
if (lean_obj_tag(v_p_u2082_655_) == 0)
{
lean_object* v_k_668_; lean_object* v_v_669_; lean_object* v_p_670_; lean_object* v_k_671_; lean_object* v___x_672_; 
lean_dec(v_h__4_659_);
v_k_668_ = lean_ctor_get(v_p_u2081_654_, 0);
lean_inc(v_k_668_);
v_v_669_ = lean_ctor_get(v_p_u2081_654_, 1);
lean_inc(v_v_669_);
v_p_670_ = lean_ctor_get(v_p_u2081_654_, 2);
lean_inc_ref(v_p_670_);
lean_dec_ref_known(v_p_u2081_654_, 3);
v_k_671_ = lean_ctor_get(v_p_u2082_655_, 0);
lean_inc(v_k_671_);
lean_dec_ref_known(v_p_u2082_655_, 1);
v___x_672_ = lean_apply_4(v_h__3_658_, v_k_668_, v_v_669_, v_p_670_, v_k_671_);
return v___x_672_;
}
else
{
lean_object* v_k_673_; lean_object* v_v_674_; lean_object* v_p_675_; lean_object* v_k_676_; lean_object* v_v_677_; lean_object* v_p_678_; lean_object* v___x_679_; 
lean_dec(v_h__3_658_);
v_k_673_ = lean_ctor_get(v_p_u2081_654_, 0);
lean_inc(v_k_673_);
v_v_674_ = lean_ctor_get(v_p_u2081_654_, 1);
lean_inc(v_v_674_);
v_p_675_ = lean_ctor_get(v_p_u2081_654_, 2);
lean_inc_ref(v_p_675_);
lean_dec_ref_known(v_p_u2081_654_, 3);
v_k_676_ = lean_ctor_get(v_p_u2082_655_, 0);
lean_inc(v_k_676_);
v_v_677_ = lean_ctor_get(v_p_u2082_655_, 1);
lean_inc(v_v_677_);
v_p_678_ = lean_ctor_get(v_p_u2082_655_, 2);
lean_inc_ref(v_p_678_);
lean_dec_ref_known(v_p_u2082_655_, 3);
v___x_679_ = lean_apply_6(v_h__4_659_, v_k_673_, v_v_674_, v_p_675_, v_k_676_, v_v_677_, v_p_678_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_combine_x27_match__1_splitter(lean_object* v_motive_680_, lean_object* v_p_u2081_681_, lean_object* v_p_u2082_682_, lean_object* v_h__1_683_, lean_object* v_h__2_684_, lean_object* v_h__3_685_, lean_object* v_h__4_686_){
_start:
{
if (lean_obj_tag(v_p_u2081_681_) == 0)
{
lean_dec(v_h__4_686_);
lean_dec(v_h__3_685_);
if (lean_obj_tag(v_p_u2082_682_) == 0)
{
lean_object* v_k_687_; lean_object* v_k_688_; lean_object* v___x_689_; 
lean_dec(v_h__2_684_);
v_k_687_ = lean_ctor_get(v_p_u2081_681_, 0);
lean_inc(v_k_687_);
lean_dec_ref_known(v_p_u2081_681_, 1);
v_k_688_ = lean_ctor_get(v_p_u2082_682_, 0);
lean_inc(v_k_688_);
lean_dec_ref_known(v_p_u2082_682_, 1);
v___x_689_ = lean_apply_2(v_h__1_683_, v_k_687_, v_k_688_);
return v___x_689_;
}
else
{
lean_object* v_k_690_; lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_p_693_; lean_object* v___x_694_; 
lean_dec(v_h__1_683_);
v_k_690_ = lean_ctor_get(v_p_u2081_681_, 0);
lean_inc(v_k_690_);
lean_dec_ref_known(v_p_u2081_681_, 1);
v_k_691_ = lean_ctor_get(v_p_u2082_682_, 0);
lean_inc(v_k_691_);
v_v_692_ = lean_ctor_get(v_p_u2082_682_, 1);
lean_inc(v_v_692_);
v_p_693_ = lean_ctor_get(v_p_u2082_682_, 2);
lean_inc_ref(v_p_693_);
lean_dec_ref_known(v_p_u2082_682_, 3);
v___x_694_ = lean_apply_4(v_h__2_684_, v_k_690_, v_k_691_, v_v_692_, v_p_693_);
return v___x_694_;
}
}
else
{
lean_dec(v_h__2_684_);
lean_dec(v_h__1_683_);
if (lean_obj_tag(v_p_u2082_682_) == 0)
{
lean_object* v_k_695_; lean_object* v_v_696_; lean_object* v_p_697_; lean_object* v_k_698_; lean_object* v___x_699_; 
lean_dec(v_h__4_686_);
v_k_695_ = lean_ctor_get(v_p_u2081_681_, 0);
lean_inc(v_k_695_);
v_v_696_ = lean_ctor_get(v_p_u2081_681_, 1);
lean_inc(v_v_696_);
v_p_697_ = lean_ctor_get(v_p_u2081_681_, 2);
lean_inc_ref(v_p_697_);
lean_dec_ref_known(v_p_u2081_681_, 3);
v_k_698_ = lean_ctor_get(v_p_u2082_682_, 0);
lean_inc(v_k_698_);
lean_dec_ref_known(v_p_u2082_682_, 1);
v___x_699_ = lean_apply_4(v_h__3_685_, v_k_695_, v_v_696_, v_p_697_, v_k_698_);
return v___x_699_;
}
else
{
lean_object* v_k_700_; lean_object* v_v_701_; lean_object* v_p_702_; lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v_p_705_; lean_object* v___x_706_; 
lean_dec(v_h__3_685_);
v_k_700_ = lean_ctor_get(v_p_u2081_681_, 0);
lean_inc(v_k_700_);
v_v_701_ = lean_ctor_get(v_p_u2081_681_, 1);
lean_inc(v_v_701_);
v_p_702_ = lean_ctor_get(v_p_u2081_681_, 2);
lean_inc_ref(v_p_702_);
lean_dec_ref_known(v_p_u2081_681_, 3);
v_k_703_ = lean_ctor_get(v_p_u2082_682_, 0);
lean_inc(v_k_703_);
v_v_704_ = lean_ctor_get(v_p_u2082_682_, 1);
lean_inc(v_v_704_);
v_p_705_ = lean_ctor_get(v_p_u2082_682_, 2);
lean_inc_ref(v_p_705_);
lean_dec_ref_known(v_p_u2082_682_, 3);
v___x_706_ = lean_apply_6(v_h__4_686_, v_k_700_, v_v_701_, v_p_702_, v_k_703_, v_v_704_, v_p_705_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* v_x_707_, lean_object* v_h__1_708_, lean_object* v_h__2_709_, lean_object* v_h__3_710_, lean_object* v_h__4_711_, lean_object* v_h__5_712_, lean_object* v_h__6_713_, lean_object* v_h__7_714_){
_start:
{
switch(lean_obj_tag(v_x_707_))
{
case 0:
{
lean_object* v_v_715_; lean_object* v___x_716_; 
lean_dec(v_h__7_714_);
lean_dec(v_h__6_713_);
lean_dec(v_h__5_712_);
lean_dec(v_h__4_711_);
lean_dec(v_h__3_710_);
lean_dec(v_h__2_709_);
v_v_715_ = lean_ctor_get(v_x_707_, 0);
lean_inc(v_v_715_);
lean_dec_ref_known(v_x_707_, 1);
v___x_716_ = lean_apply_1(v_h__1_708_, v_v_715_);
return v___x_716_;
}
case 1:
{
lean_object* v_i_717_; lean_object* v___x_718_; 
lean_dec(v_h__7_714_);
lean_dec(v_h__6_713_);
lean_dec(v_h__5_712_);
lean_dec(v_h__4_711_);
lean_dec(v_h__3_710_);
lean_dec(v_h__1_708_);
v_i_717_ = lean_ctor_get(v_x_707_, 0);
lean_inc(v_i_717_);
lean_dec_ref_known(v_x_707_, 1);
v___x_718_ = lean_apply_1(v_h__2_709_, v_i_717_);
return v___x_718_;
}
case 2:
{
lean_object* v_a_719_; lean_object* v_b_720_; lean_object* v___x_721_; 
lean_dec(v_h__7_714_);
lean_dec(v_h__6_713_);
lean_dec(v_h__5_712_);
lean_dec(v_h__4_711_);
lean_dec(v_h__2_709_);
lean_dec(v_h__1_708_);
v_a_719_ = lean_ctor_get(v_x_707_, 0);
lean_inc_ref(v_a_719_);
v_b_720_ = lean_ctor_get(v_x_707_, 1);
lean_inc_ref(v_b_720_);
lean_dec_ref_known(v_x_707_, 2);
v___x_721_ = lean_apply_2(v_h__3_710_, v_a_719_, v_b_720_);
return v___x_721_;
}
case 3:
{
lean_object* v_a_722_; lean_object* v_b_723_; lean_object* v___x_724_; 
lean_dec(v_h__7_714_);
lean_dec(v_h__6_713_);
lean_dec(v_h__5_712_);
lean_dec(v_h__3_710_);
lean_dec(v_h__2_709_);
lean_dec(v_h__1_708_);
v_a_722_ = lean_ctor_get(v_x_707_, 0);
lean_inc_ref(v_a_722_);
v_b_723_ = lean_ctor_get(v_x_707_, 1);
lean_inc_ref(v_b_723_);
lean_dec_ref_known(v_x_707_, 2);
v___x_724_ = lean_apply_2(v_h__4_711_, v_a_722_, v_b_723_);
return v___x_724_;
}
case 4:
{
lean_object* v_a_725_; lean_object* v___x_726_; 
lean_dec(v_h__6_713_);
lean_dec(v_h__5_712_);
lean_dec(v_h__4_711_);
lean_dec(v_h__3_710_);
lean_dec(v_h__2_709_);
lean_dec(v_h__1_708_);
v_a_725_ = lean_ctor_get(v_x_707_, 0);
lean_inc_ref(v_a_725_);
lean_dec_ref_known(v_x_707_, 1);
v___x_726_ = lean_apply_1(v_h__7_714_, v_a_725_);
return v___x_726_;
}
case 5:
{
lean_object* v_k_727_; lean_object* v_a_728_; lean_object* v___x_729_; 
lean_dec(v_h__7_714_);
lean_dec(v_h__6_713_);
lean_dec(v_h__4_711_);
lean_dec(v_h__3_710_);
lean_dec(v_h__2_709_);
lean_dec(v_h__1_708_);
v_k_727_ = lean_ctor_get(v_x_707_, 0);
lean_inc(v_k_727_);
v_a_728_ = lean_ctor_get(v_x_707_, 1);
lean_inc_ref(v_a_728_);
lean_dec_ref_known(v_x_707_, 2);
v___x_729_ = lean_apply_2(v_h__5_712_, v_k_727_, v_a_728_);
return v___x_729_;
}
default: 
{
lean_object* v_a_730_; lean_object* v_k_731_; lean_object* v___x_732_; 
lean_dec(v_h__7_714_);
lean_dec(v_h__5_712_);
lean_dec(v_h__4_711_);
lean_dec(v_h__3_710_);
lean_dec(v_h__2_709_);
lean_dec(v_h__1_708_);
v_a_730_ = lean_ctor_get(v_x_707_, 0);
lean_inc_ref(v_a_730_);
v_k_731_ = lean_ctor_get(v_x_707_, 1);
lean_inc(v_k_731_);
lean_dec_ref_known(v_x_707_, 2);
v___x_732_ = lean_apply_2(v_h__6_713_, v_a_730_, v_k_731_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* v_motive_733_, lean_object* v_x_734_, lean_object* v_h__1_735_, lean_object* v_h__2_736_, lean_object* v_h__3_737_, lean_object* v_h__4_738_, lean_object* v_h__5_739_, lean_object* v_h__6_740_, lean_object* v_h__7_741_){
_start:
{
switch(lean_obj_tag(v_x_734_))
{
case 0:
{
lean_object* v_v_742_; lean_object* v___x_743_; 
lean_dec(v_h__7_741_);
lean_dec(v_h__6_740_);
lean_dec(v_h__5_739_);
lean_dec(v_h__4_738_);
lean_dec(v_h__3_737_);
lean_dec(v_h__2_736_);
v_v_742_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_v_742_);
lean_dec_ref_known(v_x_734_, 1);
v___x_743_ = lean_apply_1(v_h__1_735_, v_v_742_);
return v___x_743_;
}
case 1:
{
lean_object* v_i_744_; lean_object* v___x_745_; 
lean_dec(v_h__7_741_);
lean_dec(v_h__6_740_);
lean_dec(v_h__5_739_);
lean_dec(v_h__4_738_);
lean_dec(v_h__3_737_);
lean_dec(v_h__1_735_);
v_i_744_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_i_744_);
lean_dec_ref_known(v_x_734_, 1);
v___x_745_ = lean_apply_1(v_h__2_736_, v_i_744_);
return v___x_745_;
}
case 2:
{
lean_object* v_a_746_; lean_object* v_b_747_; lean_object* v___x_748_; 
lean_dec(v_h__7_741_);
lean_dec(v_h__6_740_);
lean_dec(v_h__5_739_);
lean_dec(v_h__4_738_);
lean_dec(v_h__2_736_);
lean_dec(v_h__1_735_);
v_a_746_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_a_746_);
v_b_747_ = lean_ctor_get(v_x_734_, 1);
lean_inc_ref(v_b_747_);
lean_dec_ref_known(v_x_734_, 2);
v___x_748_ = lean_apply_2(v_h__3_737_, v_a_746_, v_b_747_);
return v___x_748_;
}
case 3:
{
lean_object* v_a_749_; lean_object* v_b_750_; lean_object* v___x_751_; 
lean_dec(v_h__7_741_);
lean_dec(v_h__6_740_);
lean_dec(v_h__5_739_);
lean_dec(v_h__3_737_);
lean_dec(v_h__2_736_);
lean_dec(v_h__1_735_);
v_a_749_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_a_749_);
v_b_750_ = lean_ctor_get(v_x_734_, 1);
lean_inc_ref(v_b_750_);
lean_dec_ref_known(v_x_734_, 2);
v___x_751_ = lean_apply_2(v_h__4_738_, v_a_749_, v_b_750_);
return v___x_751_;
}
case 4:
{
lean_object* v_a_752_; lean_object* v___x_753_; 
lean_dec(v_h__6_740_);
lean_dec(v_h__5_739_);
lean_dec(v_h__4_738_);
lean_dec(v_h__3_737_);
lean_dec(v_h__2_736_);
lean_dec(v_h__1_735_);
v_a_752_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_a_752_);
lean_dec_ref_known(v_x_734_, 1);
v___x_753_ = lean_apply_1(v_h__7_741_, v_a_752_);
return v___x_753_;
}
case 5:
{
lean_object* v_k_754_; lean_object* v_a_755_; lean_object* v___x_756_; 
lean_dec(v_h__7_741_);
lean_dec(v_h__6_740_);
lean_dec(v_h__4_738_);
lean_dec(v_h__3_737_);
lean_dec(v_h__2_736_);
lean_dec(v_h__1_735_);
v_k_754_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_k_754_);
v_a_755_ = lean_ctor_get(v_x_734_, 1);
lean_inc_ref(v_a_755_);
lean_dec_ref_known(v_x_734_, 2);
v___x_756_ = lean_apply_2(v_h__5_739_, v_k_754_, v_a_755_);
return v___x_756_;
}
default: 
{
lean_object* v_a_757_; lean_object* v_k_758_; lean_object* v___x_759_; 
lean_dec(v_h__7_741_);
lean_dec(v_h__5_739_);
lean_dec(v_h__4_738_);
lean_dec(v_h__3_737_);
lean_dec(v_h__2_736_);
lean_dec(v_h__1_735_);
v_a_757_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_a_757_);
v_k_758_ = lean_ctor_get(v_x_734_, 1);
lean_inc(v_k_758_);
lean_dec_ref_known(v_x_734_, 2);
v___x_759_ = lean_apply_2(v_h__6_740_, v_a_757_, v_k_758_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object* v_p_760_){
_start:
{
if (lean_obj_tag(v_p_760_) == 0)
{
lean_object* v_k_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_k_761_ = lean_ctor_get(v_p_760_, 0);
v___x_762_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_763_ = lean_int_dec_eq(v_k_761_, v___x_762_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; 
v___x_764_ = 1;
return v___x_764_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = 0;
return v___x_765_;
}
}
else
{
uint8_t v___x_766_; 
v___x_766_ = 0;
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatEq___boxed(lean_object* v_p_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Int_Internal_Linear_Poly_isUnsatEq(v_p_767_);
lean_dec_ref(v_p_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object* v_p_770_){
_start:
{
if (lean_obj_tag(v_p_770_) == 0)
{
lean_object* v_k_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_k_771_ = lean_ctor_get(v_p_770_, 0);
v___x_772_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_773_ = lean_int_dec_eq(v_k_771_, v___x_772_);
return v___x_773_;
}
else
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidEq___boxed(lean_object* v_p_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_Int_Internal_Linear_Poly_isValidEq(v_p_775_);
lean_dec_ref(v_p_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* v_p_778_, lean_object* v_h__1_779_, lean_object* v_h__2_780_){
_start:
{
if (lean_obj_tag(v_p_778_) == 0)
{
lean_object* v_k_781_; lean_object* v___x_782_; 
lean_dec(v_h__2_780_);
v_k_781_ = lean_ctor_get(v_p_778_, 0);
lean_inc(v_k_781_);
lean_dec_ref_known(v_p_778_, 1);
v___x_782_ = lean_apply_1(v_h__1_779_, v_k_781_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; 
lean_dec(v_h__1_779_);
v___x_783_ = lean_apply_2(v_h__2_780_, v_p_778_, lean_box(0));
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* v_motive_784_, lean_object* v_p_785_, lean_object* v_h__1_786_, lean_object* v_h__2_787_){
_start:
{
if (lean_obj_tag(v_p_785_) == 0)
{
lean_object* v_k_788_; lean_object* v___x_789_; 
lean_dec(v_h__2_787_);
v_k_788_ = lean_ctor_get(v_p_785_, 0);
lean_inc(v_k_788_);
lean_dec_ref_known(v_p_785_, 1);
v___x_789_ = lean_apply_1(v_h__1_786_, v_k_788_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; 
lean_dec(v_h__1_786_);
v___x_790_ = lean_apply_2(v_h__2_787_, v_p_785_, lean_box(0));
return v___x_790_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object* v_p_791_){
_start:
{
if (lean_obj_tag(v_p_791_) == 0)
{
lean_object* v_k_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_k_792_ = lean_ctor_get(v_p_791_, 0);
v___x_793_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_794_ = lean_int_dec_lt(v___x_793_, v_k_792_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatLe___boxed(lean_object* v_p_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_796_);
lean_dec_ref(v_p_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object* v_p_799_){
_start:
{
if (lean_obj_tag(v_p_799_) == 0)
{
lean_object* v_k_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_k_800_ = lean_ctor_get(v_p_799_, 0);
v___x_801_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_802_ = lean_int_dec_le(v_k_800_, v___x_801_);
return v___x_802_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isValidLe___boxed(lean_object* v_p_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Int_Internal_Linear_Poly_isValidLe(v_p_804_);
lean_dec_ref(v_p_804_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(lean_object* v_a_807_, lean_object* v_b_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Int_gcd(v_a_807_, v_b_808_);
v___x_810_ = lean_nat_to_int(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd___boxed(lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_gcd(v_a_811_, v_b_812_);
lean_dec(v_b_812_);
lean_dec(v_a_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
return v_x_815_;
}
else
{
lean_object* v_k_816_; lean_object* v_p_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_k_816_ = lean_ctor_get(v_x_814_, 0);
v_p_817_ = lean_ctor_get(v_x_814_, 2);
v___x_818_ = l_Int_gcd(v_k_816_, v_x_815_);
lean_dec(v_x_815_);
v___x_819_ = lean_nat_to_int(v___x_818_);
v_x_814_ = v_p_817_;
v_x_815_ = v___x_819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs___boxed(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_x_821_, v_x_822_);
lean_dec_ref(v_x_821_);
return v_res_823_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object* v_k_824_, lean_object* v_p_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_826_ = l_Int_Internal_Linear_Poly_getConst(v_p_825_);
v___x_827_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_825_, v_k_824_);
v___x_828_ = lean_int_emod(v___x_826_, v___x_827_);
lean_dec(v___x_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_830_ = lean_int_dec_eq(v___x_828_, v___x_829_);
lean_dec(v___x_828_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = 1;
return v___x_831_;
}
else
{
uint8_t v___x_832_; 
v___x_832_ = 0;
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDvd___boxed(lean_object* v_k_833_, lean_object* v_p_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_k_833_, v_p_834_);
lean_dec_ref(v_p_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_bmodCoeffs(lean_object* v_m_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_object* v_k_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_k_839_ = lean_ctor_get(v_x_838_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_838_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v_x_838_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_k_839_);
lean_dec(v_x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = l_Int_bmod(v_k_839_, v_m_837_);
lean_dec(v_k_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v_p_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_862_; 
v_k_848_ = lean_ctor_get(v_x_838_, 0);
v_v_849_ = lean_ctor_get(v_x_838_, 1);
v_p_850_ = lean_ctor_get(v_x_838_, 2);
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_838_);
if (v_isSharedCheck_862_ == 0)
{
v___x_852_ = v_x_838_;
v_isShared_853_ = v_isSharedCheck_862_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_p_850_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
lean_dec(v_x_838_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_862_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_k_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
lean_inc(v_m_837_);
v_k_854_ = l_Int_bmod(v_k_848_, v_m_837_);
lean_dec(v_k_848_);
v___x_855_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_856_ = lean_int_dec_eq(v_k_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = l_Int_Internal_Linear_Poly_bmodCoeffs(v_m_837_, v_p_850_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 2, v___x_857_);
lean_ctor_set(v___x_852_, 0, v_k_854_);
v___x_859_ = v___x_852_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_k_854_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_dec(v_k_854_);
lean_del_object(v___x_852_);
lean_dec(v_v_849_);
v_x_838_ = v_p_850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object* v_p_863_){
_start:
{
if (lean_obj_tag(v_p_863_) == 1)
{
lean_object* v_k_864_; 
v_k_864_ = lean_ctor_get(v_p_863_, 0);
lean_inc(v_k_864_);
return v_k_864_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = lean_obj_once(&l_Int_Internal_Linear_Expr_toPoly_x27___closed__0, &l_Int_Internal_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Internal_Linear_Expr_toPoly_x27___closed__0);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_leadCoeff___boxed(lean_object* v_p_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_866_);
lean_dec_ref(v_p_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object* v_p_868_, lean_object* v_x_869_){
_start:
{
if (lean_obj_tag(v_p_868_) == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
return v___x_870_;
}
else
{
lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_p_873_; uint8_t v___x_874_; 
v_k_871_ = lean_ctor_get(v_p_868_, 0);
v_v_872_ = lean_ctor_get(v_p_868_, 1);
v_p_873_ = lean_ctor_get(v_p_868_, 2);
v___x_874_ = lean_nat_dec_eq(v_x_869_, v_v_872_);
if (v___x_874_ == 0)
{
v_p_868_ = v_p_873_;
goto _start;
}
else
{
lean_inc(v_k_871_);
return v_k_871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_coeff___boxed(lean_object* v_p_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Int_Internal_Linear_Poly_coeff(v_p_876_, v_x_877_);
lean_dec(v_x_877_);
lean_dec_ref(v_p_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs(lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_nat_abs(v_x_879_);
v___x_881_ = lean_nat_to_int(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_abs___boxed(lean_object* v_x_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Int_Internal_Linear_abs(v_x_882_);
lean_dec(v_x_882_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isUnsatDiseq(lean_object* v_p_884_){
_start:
{
if (lean_obj_tag(v_p_884_) == 0)
{
lean_object* v_k_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_k_885_ = lean_ctor_get(v_p_884_, 0);
v___x_886_ = lean_obj_once(&l_Int_Internal_Linear_instInhabitedExpr_default___closed__0, &l_Int_Internal_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Internal_Linear_instInhabitedExpr_default___closed__0);
v___x_887_ = lean_int_dec_eq(v_k_885_, v___x_886_);
return v___x_887_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = 0;
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isUnsatDiseq___boxed(lean_object* v_p_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Int_Internal_Linear_Poly_isUnsatDiseq(v_p_889_);
lean_dec_ref(v_p_889_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail(lean_object* v_p_892_){
_start:
{
if (lean_obj_tag(v_p_892_) == 1)
{
lean_object* v_p_893_; 
v_p_893_ = lean_ctor_get(v_p_892_, 2);
lean_inc_ref(v_p_893_);
return v_p_893_;
}
else
{
lean_inc_ref(v_p_892_);
return v_p_892_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_tail___boxed(lean_object* v_p_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Int_Internal_Linear_Poly_tail(v_p_894_);
lean_dec_ref(v_p_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object* v_p_896_, lean_object* v_h__1_897_, lean_object* v_h__2_898_){
_start:
{
if (lean_obj_tag(v_p_896_) == 1)
{
lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_p_901_; lean_object* v___x_902_; 
lean_dec(v_h__2_898_);
v_k_899_ = lean_ctor_get(v_p_896_, 0);
lean_inc(v_k_899_);
v_v_900_ = lean_ctor_get(v_p_896_, 1);
lean_inc(v_v_900_);
v_p_901_ = lean_ctor_get(v_p_896_, 2);
lean_inc_ref(v_p_901_);
lean_dec_ref_known(v_p_896_, 3);
v___x_902_ = lean_apply_3(v_h__1_897_, v_k_899_, v_v_900_, v_p_901_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_dec(v_h__1_897_);
v___x_903_ = lean_apply_2(v_h__2_898_, v_p_896_, lean_box(0));
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Internal_Linear_Poly_leadCoeff_match__1_splitter(lean_object* v_motive_904_, lean_object* v_p_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_){
_start:
{
if (lean_obj_tag(v_p_905_) == 1)
{
lean_object* v_k_908_; lean_object* v_v_909_; lean_object* v_p_910_; lean_object* v___x_911_; 
lean_dec(v_h__2_907_);
v_k_908_ = lean_ctor_get(v_p_905_, 0);
lean_inc(v_k_908_);
v_v_909_ = lean_ctor_get(v_p_905_, 1);
lean_inc(v_v_909_);
v_p_910_ = lean_ctor_get(v_p_905_, 2);
lean_inc_ref(v_p_910_);
lean_dec_ref_known(v_p_905_, 3);
v___x_911_ = lean_apply_3(v_h__1_906_, v_k_908_, v_v_909_, v_p_910_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; 
lean_dec(v_h__1_906_);
v___x_912_ = lean_apply_2(v_h__2_907_, v_p_905_, lean_box(0));
return v___x_912_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnAdd(lean_object* v_p_913_, lean_object* v_k_914_){
_start:
{
if (lean_obj_tag(v_p_913_) == 0)
{
uint8_t v___x_915_; 
lean_dec_ref_known(v_p_913_, 1);
lean_dec_ref(v_k_914_);
v___x_915_ = 0;
return v___x_915_;
}
else
{
lean_object* v_a_916_; lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_a_916_ = lean_ctor_get(v_p_913_, 0);
lean_inc(v_a_916_);
v_a_917_ = lean_ctor_get(v_p_913_, 1);
lean_inc(v_a_917_);
v_a_918_ = lean_ctor_get(v_p_913_, 2);
lean_inc_ref(v_a_918_);
lean_dec_ref_known(v_p_913_, 3);
v___x_919_ = lean_apply_3(v_k_914_, v_a_916_, v_a_917_, v_a_918_);
v___x_920_ = lean_unbox(v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnAdd___boxed(lean_object* v_p_921_, lean_object* v_k_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Int_Internal_Linear_Poly_casesOnAdd(v_p_921_, v_k_922_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_casesOnNum(lean_object* v_p_925_, lean_object* v_k_926_){
_start:
{
if (lean_obj_tag(v_p_925_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_a_927_ = lean_ctor_get(v_p_925_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v_p_925_, 1);
v___x_928_ = lean_apply_1(v_k_926_, v_a_927_);
v___x_929_ = lean_unbox(v___x_928_);
return v___x_929_;
}
else
{
uint8_t v___x_930_; 
lean_dec_ref_known(v_p_925_, 3);
lean_dec_ref(v_k_926_);
v___x_930_ = 0;
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_casesOnNum___boxed(lean_object* v_p_931_, lean_object* v_k_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Int_Internal_Linear_Poly_casesOnNum(v_p_931_, v_k_932_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Kernel(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Int_Kernel(builtin);
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
lean_object* initialize_Init_Data_Int_Kernel(uint8_t builtin);
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
res = initialize_Init_Data_Int_Kernel(builtin);
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
