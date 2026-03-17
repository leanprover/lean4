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
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_sub_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_sub_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulL_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulL_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_Linear_instInhabitedExpr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_instInhabitedExpr_default___closed__0;
static lean_once_cell_t l_Int_Linear_instInhabitedExpr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_instInhabitedExpr_default___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_instInhabitedExpr_default;
LEAN_EXPORT lean_object* l_Int_Linear_instInhabitedExpr;
LEAN_EXPORT uint8_t l_Int_Linear_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Linear_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Linear_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Linear_instBEqExpr___closed__0 = (const lean_object*)&l_Int_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Linear_instBEqExpr = (const lean_object*)&l_Int_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instBEqPoly_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Linear_instBEqPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Linear_instBEqPoly_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Linear_instBEqPoly___closed__0 = (const lean_object*)&l_Int_Linear_instBEqPoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Linear_instBEqPoly = (const lean_object*)&l_Int_Linear_instBEqPoly___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_instBEqPoly_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_instBEqPoly_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_hugeFuel;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_Linear_Expr_toPoly_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Expr_toPoly_x27___closed__0;
static lean_once_cell_t l_Int_Linear_Expr_toPoly_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Expr_toPoly_x27___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_cmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divCoeffs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatEq___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatLe___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidLe___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDvd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_abs(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_abs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDiseq(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDiseq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnAdd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_emod__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_emod__le__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_not__le__of__le__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_not__le__of__le__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote(lean_object* v_ctx_1_, lean_object* v_v_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_RArray_getImpl___redArg(v_ctx_1_, v_v_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Var_denote___boxed(lean_object* v_ctx_4_, lean_object* v_v_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Int_Linear_Var_denote(v_ctx_4_, v_v_5_);
lean_dec(v_v_5_);
lean_dec_ref(v_ctx_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorIdx(lean_object* v_x_7_){
_start:
{
switch(lean_obj_tag(v_x_7_))
{
case 0:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(0u);
return v___x_8_;
}
case 1:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(1u);
return v___x_9_;
}
case 2:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(2u);
return v___x_10_;
}
case 3:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(3u);
return v___x_11_;
}
case 4:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(4u);
return v___x_12_;
}
case 5:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(5u);
return v___x_13_;
}
default: 
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(6u);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorIdx___boxed(lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Int_Linear_Expr_ctorIdx(v_x_15_);
lean_dec_ref(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorElim___redArg(lean_object* v_t_17_, lean_object* v_k_18_){
_start:
{
switch(lean_obj_tag(v_t_17_))
{
case 2:
{
lean_object* v_a_19_; lean_object* v_b_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v_t_17_, 0);
lean_inc_ref(v_a_19_);
v_b_20_ = lean_ctor_get(v_t_17_, 1);
lean_inc_ref(v_b_20_);
lean_dec_ref(v_t_17_);
v___x_21_ = lean_apply_2(v_k_18_, v_a_19_, v_b_20_);
return v___x_21_;
}
case 3:
{
lean_object* v_a_22_; lean_object* v_b_23_; lean_object* v___x_24_; 
v_a_22_ = lean_ctor_get(v_t_17_, 0);
lean_inc_ref(v_a_22_);
v_b_23_ = lean_ctor_get(v_t_17_, 1);
lean_inc_ref(v_b_23_);
lean_dec_ref(v_t_17_);
v___x_24_ = lean_apply_2(v_k_18_, v_a_22_, v_b_23_);
return v___x_24_;
}
case 4:
{
lean_object* v_a_25_; lean_object* v___x_26_; 
v_a_25_ = lean_ctor_get(v_t_17_, 0);
lean_inc_ref(v_a_25_);
lean_dec_ref(v_t_17_);
v___x_26_ = lean_apply_1(v_k_18_, v_a_25_);
return v___x_26_;
}
case 5:
{
lean_object* v_k_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
v_k_27_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_k_27_);
v_a_28_ = lean_ctor_get(v_t_17_, 1);
lean_inc_ref(v_a_28_);
lean_dec_ref(v_t_17_);
v___x_29_ = lean_apply_2(v_k_18_, v_k_27_, v_a_28_);
return v___x_29_;
}
case 6:
{
lean_object* v_a_30_; lean_object* v_k_31_; lean_object* v___x_32_; 
v_a_30_ = lean_ctor_get(v_t_17_, 0);
lean_inc_ref(v_a_30_);
v_k_31_ = lean_ctor_get(v_t_17_, 1);
lean_inc(v_k_31_);
lean_dec_ref(v_t_17_);
v___x_32_ = lean_apply_2(v_k_18_, v_a_30_, v_k_31_);
return v___x_32_;
}
default: 
{
lean_object* v_v_33_; lean_object* v___x_34_; 
v_v_33_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_v_33_);
lean_dec_ref(v_t_17_);
v___x_34_ = lean_apply_1(v_k_18_, v_v_33_);
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorElim(lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_37_, v_k_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_ctorElim___boxed(lean_object* v_motive_41_, lean_object* v_ctorIdx_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_k_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Int_Linear_Expr_ctorElim(v_motive_41_, v_ctorIdx_42_, v_t_43_, v_h_44_, v_k_45_);
lean_dec(v_ctorIdx_42_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_num_elim___redArg(lean_object* v_t_47_, lean_object* v_num_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_47_, v_num_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_num_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_num_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_51_, v_num_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_var_elim___redArg(lean_object* v_t_55_, lean_object* v_var_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_55_, v_var_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_var_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_var_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_59_, v_var_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_add_elim___redArg(lean_object* v_t_63_, lean_object* v_add_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_63_, v_add_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_add_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_add_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_67_, v_add_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_sub_elim___redArg(lean_object* v_t_71_, lean_object* v_sub_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_71_, v_sub_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_sub_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_sub_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_75_, v_sub_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_neg_elim___redArg(lean_object* v_t_79_, lean_object* v_neg_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_79_, v_neg_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_neg_elim(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_neg_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_83_, v_neg_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulL_elim___redArg(lean_object* v_t_87_, lean_object* v_mulL_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_87_, v_mulL_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulL_elim(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_mulL_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_91_, v_mulL_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulR_elim___redArg(lean_object* v_t_95_, lean_object* v_mulR_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_95_, v_mulR_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_mulR_elim(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_mulR_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Int_Linear_Expr_ctorElim___redArg(v_t_99_, v_mulR_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr_default___closed__0(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_to_int(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr_default___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr_default(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__1, &l_Int_Linear_instInhabitedExpr_default___closed__1_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__1);
return v___x_107_;
}
}
static lean_object* _init_l_Int_Linear_instInhabitedExpr(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Int_Linear_instInhabitedExpr_default;
return v___x_108_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_instBEqExpr_beq(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v_b_114_; lean_object* v_b_115_; 
switch(lean_obj_tag(v_x_109_))
{
case 0:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v_v_118_; lean_object* v_v_119_; uint8_t v___x_120_; 
v_v_118_ = lean_ctor_get(v_x_109_, 0);
v_v_119_ = lean_ctor_get(v_x_110_, 0);
v___x_120_ = lean_int_dec_eq(v_v_118_, v_v_119_);
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
case 1:
{
if (lean_obj_tag(v_x_110_) == 1)
{
lean_object* v_i_122_; lean_object* v_i_123_; uint8_t v___x_124_; 
v_i_122_ = lean_ctor_get(v_x_109_, 0);
v_i_123_ = lean_ctor_get(v_x_110_, 0);
v___x_124_ = lean_nat_dec_eq(v_i_122_, v_i_123_);
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
case 2:
{
if (lean_obj_tag(v_x_110_) == 2)
{
lean_object* v_a_126_; lean_object* v_b_127_; lean_object* v_a_128_; lean_object* v_b_129_; 
v_a_126_ = lean_ctor_get(v_x_109_, 0);
v_b_127_ = lean_ctor_get(v_x_109_, 1);
v_a_128_ = lean_ctor_get(v_x_110_, 0);
v_b_129_ = lean_ctor_get(v_x_110_, 1);
v_a_112_ = v_a_126_;
v_a_113_ = v_b_127_;
v_b_114_ = v_a_128_;
v_b_115_ = v_b_129_;
goto v___jp_111_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
case 3:
{
if (lean_obj_tag(v_x_110_) == 3)
{
lean_object* v_a_131_; lean_object* v_b_132_; lean_object* v_a_133_; lean_object* v_b_134_; 
v_a_131_ = lean_ctor_get(v_x_109_, 0);
v_b_132_ = lean_ctor_get(v_x_109_, 1);
v_a_133_ = lean_ctor_get(v_x_110_, 0);
v_b_134_ = lean_ctor_get(v_x_110_, 1);
v_a_112_ = v_a_131_;
v_a_113_ = v_b_132_;
v_b_114_ = v_a_133_;
v_b_115_ = v_b_134_;
goto v___jp_111_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
case 4:
{
if (lean_obj_tag(v_x_110_) == 4)
{
lean_object* v_a_136_; lean_object* v_a_137_; 
v_a_136_ = lean_ctor_get(v_x_109_, 0);
v_a_137_ = lean_ctor_get(v_x_110_, 0);
v_x_109_ = v_a_136_;
v_x_110_ = v_a_137_;
goto _start;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
}
case 5:
{
if (lean_obj_tag(v_x_110_) == 5)
{
lean_object* v_k_140_; lean_object* v_a_141_; lean_object* v_k_142_; lean_object* v_a_143_; uint8_t v___x_144_; 
v_k_140_ = lean_ctor_get(v_x_109_, 0);
v_a_141_ = lean_ctor_get(v_x_109_, 1);
v_k_142_ = lean_ctor_get(v_x_110_, 0);
v_a_143_ = lean_ctor_get(v_x_110_, 1);
v___x_144_ = lean_int_dec_eq(v_k_140_, v_k_142_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
v_x_109_ = v_a_141_;
v_x_110_ = v_a_143_;
goto _start;
}
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
default: 
{
if (lean_obj_tag(v_x_110_) == 6)
{
lean_object* v_a_147_; lean_object* v_k_148_; lean_object* v_a_149_; lean_object* v_k_150_; uint8_t v___x_151_; 
v_a_147_ = lean_ctor_get(v_x_109_, 0);
v_k_148_ = lean_ctor_get(v_x_109_, 1);
v_a_149_ = lean_ctor_get(v_x_110_, 0);
v_k_150_ = lean_ctor_get(v_x_110_, 1);
v___x_151_ = l_Int_Linear_instBEqExpr_beq(v_a_147_, v_a_149_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
uint8_t v___x_152_; 
v___x_152_ = lean_int_dec_eq(v_k_148_, v_k_150_);
return v___x_152_;
}
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
}
v___jp_111_:
{
uint8_t v___x_116_; 
v___x_116_ = l_Int_Linear_instBEqExpr_beq(v_a_112_, v_b_114_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
v_x_109_ = v_a_113_;
v_x_110_ = v_b_115_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instBEqExpr_beq___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Int_Linear_instBEqExpr_beq(v_x_154_, v_x_155_);
lean_dec_ref(v_x_155_);
lean_dec_ref(v_x_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote(lean_object* v_ctx_160_, lean_object* v_x_161_){
_start:
{
switch(lean_obj_tag(v_x_161_))
{
case 0:
{
lean_object* v_v_162_; 
v_v_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_v_162_);
return v_v_162_;
}
case 1:
{
lean_object* v_i_163_; lean_object* v___x_164_; 
v_i_163_ = lean_ctor_get(v_x_161_, 0);
v___x_164_ = l_Lean_RArray_getImpl___redArg(v_ctx_160_, v_i_163_);
return v___x_164_;
}
case 2:
{
lean_object* v_a_165_; lean_object* v_b_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_165_ = lean_ctor_get(v_x_161_, 0);
v_b_166_ = lean_ctor_get(v_x_161_, 1);
v___x_167_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_a_165_);
v___x_168_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_b_166_);
v___x_169_ = lean_int_add(v___x_167_, v___x_168_);
lean_dec(v___x_168_);
lean_dec(v___x_167_);
return v___x_169_;
}
case 3:
{
lean_object* v_a_170_; lean_object* v_b_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_a_170_ = lean_ctor_get(v_x_161_, 0);
v_b_171_ = lean_ctor_get(v_x_161_, 1);
v___x_172_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_a_170_);
v___x_173_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_b_171_);
v___x_174_ = lean_int_sub(v___x_172_, v___x_173_);
lean_dec(v___x_173_);
lean_dec(v___x_172_);
return v___x_174_;
}
case 4:
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_a_175_ = lean_ctor_get(v_x_161_, 0);
v___x_176_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_a_175_);
v___x_177_ = lean_int_neg(v___x_176_);
lean_dec(v___x_176_);
return v___x_177_;
}
case 5:
{
lean_object* v_k_178_; lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_k_178_ = lean_ctor_get(v_x_161_, 0);
v_a_179_ = lean_ctor_get(v_x_161_, 1);
v___x_180_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_a_179_);
v___x_181_ = lean_int_mul(v_k_178_, v___x_180_);
lean_dec(v___x_180_);
return v___x_181_;
}
default: 
{
lean_object* v_a_182_; lean_object* v_k_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_182_ = lean_ctor_get(v_x_161_, 0);
v_k_183_ = lean_ctor_get(v_x_161_, 1);
v___x_184_ = l_Int_Linear_Expr_denote(v_ctx_160_, v_a_182_);
v___x_185_ = lean_int_mul(v___x_184_, v_k_183_);
lean_dec(v___x_184_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denote___boxed(lean_object* v_ctx_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Int_Linear_Expr_denote(v_ctx_186_, v_x_187_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_ctx_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorIdx(lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(1u);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorIdx___boxed(lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Int_Linear_Poly_ctorIdx(v_x_192_);
lean_dec_ref(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorElim___redArg(lean_object* v_t_194_, lean_object* v_k_195_){
_start:
{
if (lean_obj_tag(v_t_194_) == 0)
{
lean_object* v_k_196_; lean_object* v___x_197_; 
v_k_196_ = lean_ctor_get(v_t_194_, 0);
lean_inc(v_k_196_);
lean_dec_ref(v_t_194_);
v___x_197_ = lean_apply_1(v_k_195_, v_k_196_);
return v___x_197_;
}
else
{
lean_object* v_k_198_; lean_object* v_v_199_; lean_object* v_p_200_; lean_object* v___x_201_; 
v_k_198_ = lean_ctor_get(v_t_194_, 0);
lean_inc(v_k_198_);
v_v_199_ = lean_ctor_get(v_t_194_, 1);
lean_inc(v_v_199_);
v_p_200_ = lean_ctor_get(v_t_194_, 2);
lean_inc_ref(v_p_200_);
lean_dec_ref(v_t_194_);
v___x_201_ = lean_apply_3(v_k_195_, v_k_198_, v_v_199_, v_p_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorElim(lean_object* v_motive_202_, lean_object* v_ctorIdx_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_k_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_204_, v_k_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_ctorElim___boxed(lean_object* v_motive_208_, lean_object* v_ctorIdx_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_k_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Int_Linear_Poly_ctorElim(v_motive_208_, v_ctorIdx_209_, v_t_210_, v_h_211_, v_k_212_);
lean_dec(v_ctorIdx_209_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_num_elim___redArg(lean_object* v_t_214_, lean_object* v_num_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_214_, v_num_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_num_elim(lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_num_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_218_, v_num_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_add_elim___redArg(lean_object* v_t_222_, lean_object* v_add_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_222_, v_add_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_add_elim(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_add_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Int_Linear_Poly_ctorElim___redArg(v_t_226_, v_add_228_);
return v___x_229_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_instBEqPoly_beq(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v_k_232_; lean_object* v_k_233_; uint8_t v___x_234_; 
v_k_232_ = lean_ctor_get(v_x_230_, 0);
v_k_233_ = lean_ctor_get(v_x_231_, 0);
v___x_234_ = lean_int_dec_eq(v_k_232_, v_k_233_);
return v___x_234_;
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
else
{
if (lean_obj_tag(v_x_231_) == 1)
{
lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_p_238_; lean_object* v_k_239_; lean_object* v_v_240_; lean_object* v_p_241_; uint8_t v___x_242_; 
v_k_236_ = lean_ctor_get(v_x_230_, 0);
v_v_237_ = lean_ctor_get(v_x_230_, 1);
v_p_238_ = lean_ctor_get(v_x_230_, 2);
v_k_239_ = lean_ctor_get(v_x_231_, 0);
v_v_240_ = lean_ctor_get(v_x_231_, 1);
v_p_241_ = lean_ctor_get(v_x_231_, 2);
v___x_242_ = lean_int_dec_eq(v_k_236_, v_k_239_);
if (v___x_242_ == 0)
{
return v___x_242_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_eq(v_v_237_, v_v_240_);
if (v___x_243_ == 0)
{
return v___x_243_;
}
else
{
v_x_230_ = v_p_238_;
v_x_231_ = v_p_241_;
goto _start;
}
}
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instBEqPoly_beq___boxed(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Int_Linear_instBEqPoly_beq(v_x_246_, v_x_247_);
lean_dec_ref(v_x_247_);
lean_dec_ref(v_x_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_, lean_object* v_h__3_256_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_dec(v_h__2_255_);
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v_k_257_; lean_object* v_k_258_; lean_object* v___x_259_; 
lean_dec(v_h__3_256_);
v_k_257_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_k_257_);
lean_dec_ref(v_x_252_);
v_k_258_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_k_258_);
lean_dec_ref(v_x_253_);
v___x_259_ = lean_apply_2(v_h__1_254_, v_k_257_, v_k_258_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; 
lean_dec(v_h__1_254_);
v___x_260_ = lean_apply_4(v_h__3_256_, v_x_252_, v_x_253_, lean_box(0), lean_box(0));
return v___x_260_;
}
}
else
{
lean_dec(v_h__1_254_);
if (lean_obj_tag(v_x_253_) == 1)
{
lean_object* v_k_261_; lean_object* v_v_262_; lean_object* v_p_263_; lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v_p_266_; lean_object* v___x_267_; 
lean_dec(v_h__3_256_);
v_k_261_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_k_261_);
v_v_262_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_v_262_);
v_p_263_ = lean_ctor_get(v_x_252_, 2);
lean_inc_ref(v_p_263_);
lean_dec_ref(v_x_252_);
v_k_264_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_k_264_);
v_v_265_ = lean_ctor_get(v_x_253_, 1);
lean_inc(v_v_265_);
v_p_266_ = lean_ctor_get(v_x_253_, 2);
lean_inc_ref(v_p_266_);
lean_dec_ref(v_x_253_);
v___x_267_ = lean_apply_6(v_h__2_255_, v_k_261_, v_v_262_, v_p_263_, v_k_264_, v_v_265_, v_p_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
lean_dec(v_h__2_255_);
v___x_268_ = lean_apply_4(v_h__3_256_, v_x_252_, v_x_253_, lean_box(0), lean_box(0));
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_h__1_272_, lean_object* v_h__2_273_, lean_object* v_h__3_274_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_dec(v_h__2_273_);
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_k_275_; lean_object* v_k_276_; lean_object* v___x_277_; 
lean_dec(v_h__3_274_);
v_k_275_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_k_275_);
lean_dec_ref(v_x_270_);
v_k_276_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_k_276_);
lean_dec_ref(v_x_271_);
v___x_277_ = lean_apply_2(v_h__1_272_, v_k_275_, v_k_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; 
lean_dec(v_h__1_272_);
v___x_278_ = lean_apply_4(v_h__3_274_, v_x_270_, v_x_271_, lean_box(0), lean_box(0));
return v___x_278_;
}
}
else
{
lean_dec(v_h__1_272_);
if (lean_obj_tag(v_x_271_) == 1)
{
lean_object* v_k_279_; lean_object* v_v_280_; lean_object* v_p_281_; lean_object* v_k_282_; lean_object* v_v_283_; lean_object* v_p_284_; lean_object* v___x_285_; 
lean_dec(v_h__3_274_);
v_k_279_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_k_279_);
v_v_280_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_v_280_);
v_p_281_ = lean_ctor_get(v_x_270_, 2);
lean_inc_ref(v_p_281_);
lean_dec_ref(v_x_270_);
v_k_282_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_k_282_);
v_v_283_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_v_283_);
v_p_284_ = lean_ctor_get(v_x_271_, 2);
lean_inc_ref(v_p_284_);
lean_dec_ref(v_x_271_);
v___x_285_ = lean_apply_6(v_h__2_273_, v_k_279_, v_v_280_, v_p_281_, v_k_282_, v_v_283_, v_p_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; 
lean_dec(v_h__2_273_);
v___x_286_ = lean_apply_4(v_h__3_274_, v_x_270_, v_x_271_, lean_box(0), lean_box(0));
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote(lean_object* v_ctx_287_, lean_object* v_p_288_){
_start:
{
if (lean_obj_tag(v_p_288_) == 0)
{
lean_object* v_k_289_; 
v_k_289_ = lean_ctor_get(v_p_288_, 0);
lean_inc(v_k_289_);
return v_k_289_;
}
else
{
lean_object* v_k_290_; lean_object* v_v_291_; lean_object* v_p_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_k_290_ = lean_ctor_get(v_p_288_, 0);
v_v_291_ = lean_ctor_get(v_p_288_, 1);
v_p_292_ = lean_ctor_get(v_p_288_, 2);
v___x_293_ = l_Lean_RArray_getImpl___redArg(v_ctx_287_, v_v_291_);
v___x_294_ = lean_int_mul(v_k_290_, v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = l_Int_Linear_Poly_denote(v_ctx_287_, v_p_292_);
v___x_296_ = lean_int_add(v___x_294_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___x_294_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denote___boxed(lean_object* v_ctx_297_, lean_object* v_p_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Int_Linear_Poly_denote(v_ctx_297_, v_p_298_);
lean_dec_ref(v_p_298_);
lean_dec_ref(v_ctx_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(lean_object* v_p_300_, lean_object* v_h__1_301_, lean_object* v_h__2_302_){
_start:
{
if (lean_obj_tag(v_p_300_) == 0)
{
lean_object* v_k_303_; lean_object* v___x_304_; 
lean_dec(v_h__2_302_);
v_k_303_ = lean_ctor_get(v_p_300_, 0);
lean_inc(v_k_303_);
lean_dec_ref(v_p_300_);
v___x_304_ = lean_apply_1(v_h__1_301_, v_k_303_);
return v___x_304_;
}
else
{
lean_object* v_k_305_; lean_object* v_v_306_; lean_object* v_p_307_; lean_object* v___x_308_; 
lean_dec(v_h__1_301_);
v_k_305_ = lean_ctor_get(v_p_300_, 0);
lean_inc(v_k_305_);
v_v_306_ = lean_ctor_get(v_p_300_, 1);
lean_inc(v_v_306_);
v_p_307_ = lean_ctor_get(v_p_300_, 2);
lean_inc_ref(v_p_307_);
lean_dec_ref(v_p_300_);
v___x_308_ = lean_apply_3(v_h__2_302_, v_k_305_, v_v_306_, v_p_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter(lean_object* v_motive_309_, lean_object* v_p_310_, lean_object* v_h__1_311_, lean_object* v_h__2_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_denote_match__1_splitter___redArg(v_p_310_, v_h__1_311_, v_h__2_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst(lean_object* v_p_314_, lean_object* v_k_315_){
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
v___x_331_ = l_Int_Linear_Poly_addConst(v_p_327_, v_k_315_);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst___boxed(lean_object* v_p_336_, lean_object* v_k_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Int_Linear_Poly_addConst(v_p_336_, v_k_337_);
lean_dec(v_k_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_insert(lean_object* v_k_339_, lean_object* v_v_340_, lean_object* v_p_341_){
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
v___x_351_ = l_Int_Linear_Poly_insert(v_k_339_, v_v_340_, v_p_345_);
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
v___x_356_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_norm(lean_object* v_p_366_){
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
lean_dec_ref(v_p_366_);
v___x_370_ = l_Int_Linear_Poly_norm(v_p_369_);
v___x_371_ = l_Int_Linear_Poly_insert(v_k_367_, v_v_368_, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_append(lean_object* v_p_u2081_372_, lean_object* v_p_u2082_373_){
_start:
{
if (lean_obj_tag(v_p_u2081_372_) == 0)
{
lean_object* v_k_374_; lean_object* v___x_375_; 
v_k_374_ = lean_ctor_get(v_p_u2081_372_, 0);
lean_inc(v_k_374_);
lean_dec_ref(v_p_u2081_372_);
v___x_375_ = l_Int_Linear_Poly_addConst(v_p_u2082_373_, v_k_374_);
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
v___x_382_ = l_Int_Linear_Poly_append(v_p_378_, v_p_u2082_373_);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine_x27(lean_object* v_fuel_387_, lean_object* v_p_u2081_388_, lean_object* v_p_u2082_389_){
_start:
{
lean_object* v_zero_390_; uint8_t v_isZero_391_; 
v_zero_390_ = lean_unsigned_to_nat(0u);
v_isZero_391_ = lean_nat_dec_eq(v_fuel_387_, v_zero_390_);
if (v_isZero_391_ == 1)
{
lean_object* v___x_392_; 
lean_dec(v_fuel_387_);
v___x_392_ = l_Int_Linear_Poly_append(v_p_u2081_388_, v_p_u2082_389_);
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
lean_dec_ref(v_p_u2081_388_);
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
v___x_411_ = l_Int_Linear_Poly_combine_x27(v_n_394_, v_p_u2081_388_, v_p_407_);
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
v___x_422_ = l_Int_Linear_Poly_combine_x27(v_n_394_, v_p_418_, v_p_u2082_389_);
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
v___x_438_ = l_Int_Linear_Poly_combine_x27(v_n_394_, v_p_u2081_388_, v_p_432_);
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
v___x_449_ = l_Int_Linear_Poly_combine_x27(v_n_394_, v_p_429_, v_p_u2082_389_);
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
lean_dec_ref(v_p_u2081_388_);
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
v___x_461_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_462_ = lean_int_dec_eq(v_a_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = l_Int_Linear_Poly_combine_x27(v_n_394_, v_p_429_, v_p_432_);
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
static lean_object* _init_l_Int_Linear_hugeFuel(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(100000000u);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine(lean_object* v_p_u2081_473_, lean_object* v_p_u2082_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(100000000u);
v___x_476_ = l_Int_Linear_Poly_combine_x27(v___x_475_, v_p_u2081_473_, v_p_u2082_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go(lean_object* v_coeff_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
switch(lean_obj_tag(v_a_478_))
{
case 0:
{
lean_object* v_v_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_v_480_ = lean_ctor_get(v_a_478_, 0);
v___x_481_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_482_ = lean_int_dec_eq(v_v_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_int_mul(v_coeff_477_, v_v_480_);
lean_dec(v_coeff_477_);
v___x_484_ = l_Int_Linear_Poly_addConst(v_a_479_, v___x_483_);
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
v___x_489_ = l_Int_Linear_Expr_toPoly_x27_go(v_coeff_477_, v_b_488_, v_a_479_);
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
v___x_494_ = l_Int_Linear_Expr_toPoly_x27_go(v___x_493_, v_b_492_, v_a_479_);
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
v___x_501_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
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
v___x_507_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
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
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go___boxed(lean_object* v_coeff_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Int_Linear_Expr_toPoly_x27_go(v_coeff_511_, v_a_512_, v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_514_;
}
}
static lean_object* _init_l_Int_Linear_Expr_toPoly_x27___closed__0(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Int_Linear_Expr_toPoly_x27___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27(lean_object* v_e_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
v___x_521_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__1, &l_Int_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__1);
v___x_522_ = l_Int_Linear_Expr_toPoly_x27_go(v___x_520_, v_e_519_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27___boxed(lean_object* v_e_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Int_Linear_Expr_toPoly_x27(v_e_523_);
lean_dec_ref(v_e_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm(lean_object* v_e_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l_Int_Linear_Expr_toPoly_x27(v_e_525_);
v___x_527_ = l_Int_Linear_Poly_norm(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm___boxed(lean_object* v_e_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Int_Linear_Expr_norm(v_e_528_);
lean_dec_ref(v_e_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cdiv(lean_object* v_a_530_, lean_object* v_b_531_){
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
LEAN_EXPORT lean_object* l_Int_Linear_cdiv___boxed(lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Int_Linear_cdiv(v_a_535_, v_b_536_);
lean_dec(v_b_536_);
lean_dec(v_a_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cmod(lean_object* v_a_538_, lean_object* v_b_539_){
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
LEAN_EXPORT lean_object* l_Int_Linear_cmod___boxed(lean_object* v_a_543_, lean_object* v_b_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Int_Linear_cmod(v_a_543_, v_b_544_);
lean_dec(v_b_544_);
lean_dec(v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst(lean_object* v_x_546_){
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst___boxed(lean_object* v_x_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Int_Linear_Poly_getConst(v_x_550_);
lean_dec_ref(v_x_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div(lean_object* v_k_552_, lean_object* v_x_553_){
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
v___x_558_ = l_Int_Linear_cdiv(v_k_554_, v_k_552_);
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
v___x_570_ = l_Int_Linear_Poly_div(v_k_552_, v_p_565_);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div___boxed(lean_object* v_k_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Int_Linear_Poly_div(v_k_575_, v_x_576_);
lean_dec(v_k_575_);
return v_res_577_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divAll(lean_object* v_k_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_k_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_k_580_ = lean_ctor_get(v_x_579_, 0);
v___x_581_ = lean_int_emod(v_k_580_, v_k_578_);
v___x_582_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
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
v___x_587_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divAll___boxed(lean_object* v_k_590_, lean_object* v_x_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Int_Linear_Poly_divAll(v_k_590_, v_x_591_);
lean_dec_ref(v_x_591_);
lean_dec(v_k_590_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divCoeffs(lean_object* v_k_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
uint8_t v___x_596_; 
v___x_596_ = 1;
return v___x_596_;
}
else
{
lean_object* v_k_597_; lean_object* v_p_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_k_597_ = lean_ctor_get(v_x_595_, 0);
v_p_598_ = lean_ctor_get(v_x_595_, 2);
v___x_599_ = lean_int_emod(v_k_597_, v_k_594_);
v___x_600_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_601_ = lean_int_dec_eq(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
if (v___x_601_ == 0)
{
return v___x_601_;
}
else
{
v_x_595_ = v_p_598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divCoeffs___boxed(lean_object* v_k_603_, lean_object* v_x_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Int_Linear_Poly_divCoeffs(v_k_603_, v_x_604_);
lean_dec_ref(v_x_604_);
lean_dec(v_k_603_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27(lean_object* v_p_607_, lean_object* v_k_608_){
_start:
{
if (lean_obj_tag(v_p_607_) == 0)
{
lean_object* v_k_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_617_; 
v_k_609_ = lean_ctor_get(v_p_607_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_p_607_);
if (v_isSharedCheck_617_ == 0)
{
v___x_611_ = v_p_607_;
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_k_609_);
lean_dec(v_p_607_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_int_mul(v_k_608_, v_k_609_);
lean_dec(v_k_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_k_618_; lean_object* v_v_619_; lean_object* v_p_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_629_; 
v_k_618_ = lean_ctor_get(v_p_607_, 0);
v_v_619_ = lean_ctor_get(v_p_607_, 1);
v_p_620_ = lean_ctor_get(v_p_607_, 2);
v_isSharedCheck_629_ = !lean_is_exclusive(v_p_607_);
if (v_isSharedCheck_629_ == 0)
{
v___x_622_ = v_p_607_;
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_p_620_);
lean_inc(v_v_619_);
lean_inc(v_k_618_);
lean_dec(v_p_607_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_624_ = lean_int_mul(v_k_608_, v_k_618_);
lean_dec(v_k_618_);
v___x_625_ = l_Int_Linear_Poly_mul_x27(v_p_620_, v_k_608_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 2, v___x_625_);
lean_ctor_set(v___x_622_, 0, v___x_624_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_v_619_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27___boxed(lean_object* v_p_630_, lean_object* v_k_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Int_Linear_Poly_mul_x27(v_p_630_, v_k_631_);
lean_dec(v_k_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul(lean_object* v_p_633_, lean_object* v_k_634_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_636_ = lean_int_dec_eq(v_k_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = l_Int_Linear_Poly_mul_x27(v_p_633_, v_k_634_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v_p_633_);
v___x_638_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__1, &l_Int_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__1);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul___boxed(lean_object* v_p_639_, lean_object* v_k_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Int_Linear_Poly_mul(v_p_639_, v_k_640_);
lean_dec(v_k_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object* v_fuel_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
lean_object* v_zero_645_; uint8_t v_isZero_646_; 
v_zero_645_ = lean_unsigned_to_nat(0u);
v_isZero_646_ = lean_nat_dec_eq(v_fuel_642_, v_zero_645_);
if (v_isZero_646_ == 1)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_h__2_644_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_apply_1(v_h__1_643_, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_one_649_; lean_object* v_n_650_; lean_object* v___x_651_; 
lean_dec(v_h__1_643_);
v_one_649_ = lean_unsigned_to_nat(1u);
v_n_650_ = lean_nat_sub(v_fuel_642_, v_one_649_);
v___x_651_ = lean_apply_1(v_h__2_644_, v_n_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object* v_fuel_652_, lean_object* v_h__1_653_, lean_object* v_h__2_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(v_fuel_652_, v_h__1_653_, v_h__2_654_);
lean_dec(v_fuel_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(lean_object* v_motive_656_, lean_object* v_fuel_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(v_fuel_657_, v_h__1_658_, v_h__2_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object* v_motive_661_, lean_object* v_fuel_662_, lean_object* v_h__1_663_, lean_object* v_h__2_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(v_motive_661_, v_fuel_662_, v_h__1_663_, v_h__2_664_);
lean_dec(v_fuel_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object* v_p_u2081_666_, lean_object* v_p_u2082_667_, lean_object* v_h__1_668_, lean_object* v_h__2_669_, lean_object* v_h__3_670_, lean_object* v_h__4_671_){
_start:
{
if (lean_obj_tag(v_p_u2081_666_) == 0)
{
lean_dec(v_h__4_671_);
lean_dec(v_h__3_670_);
if (lean_obj_tag(v_p_u2082_667_) == 0)
{
lean_object* v_k_672_; lean_object* v_k_673_; lean_object* v___x_674_; 
lean_dec(v_h__2_669_);
v_k_672_ = lean_ctor_get(v_p_u2081_666_, 0);
lean_inc(v_k_672_);
lean_dec_ref(v_p_u2081_666_);
v_k_673_ = lean_ctor_get(v_p_u2082_667_, 0);
lean_inc(v_k_673_);
lean_dec_ref(v_p_u2082_667_);
v___x_674_ = lean_apply_2(v_h__1_668_, v_k_672_, v_k_673_);
return v___x_674_;
}
else
{
lean_object* v_k_675_; lean_object* v_k_676_; lean_object* v_v_677_; lean_object* v_p_678_; lean_object* v___x_679_; 
lean_dec(v_h__1_668_);
v_k_675_ = lean_ctor_get(v_p_u2081_666_, 0);
lean_inc(v_k_675_);
lean_dec_ref(v_p_u2081_666_);
v_k_676_ = lean_ctor_get(v_p_u2082_667_, 0);
lean_inc(v_k_676_);
v_v_677_ = lean_ctor_get(v_p_u2082_667_, 1);
lean_inc(v_v_677_);
v_p_678_ = lean_ctor_get(v_p_u2082_667_, 2);
lean_inc_ref(v_p_678_);
lean_dec_ref(v_p_u2082_667_);
v___x_679_ = lean_apply_4(v_h__2_669_, v_k_675_, v_k_676_, v_v_677_, v_p_678_);
return v___x_679_;
}
}
else
{
lean_dec(v_h__2_669_);
lean_dec(v_h__1_668_);
if (lean_obj_tag(v_p_u2082_667_) == 0)
{
lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v_p_682_; lean_object* v_k_683_; lean_object* v___x_684_; 
lean_dec(v_h__4_671_);
v_k_680_ = lean_ctor_get(v_p_u2081_666_, 0);
lean_inc(v_k_680_);
v_v_681_ = lean_ctor_get(v_p_u2081_666_, 1);
lean_inc(v_v_681_);
v_p_682_ = lean_ctor_get(v_p_u2081_666_, 2);
lean_inc_ref(v_p_682_);
lean_dec_ref(v_p_u2081_666_);
v_k_683_ = lean_ctor_get(v_p_u2082_667_, 0);
lean_inc(v_k_683_);
lean_dec_ref(v_p_u2082_667_);
v___x_684_ = lean_apply_4(v_h__3_670_, v_k_680_, v_v_681_, v_p_682_, v_k_683_);
return v___x_684_;
}
else
{
lean_object* v_k_685_; lean_object* v_v_686_; lean_object* v_p_687_; lean_object* v_k_688_; lean_object* v_v_689_; lean_object* v_p_690_; lean_object* v___x_691_; 
lean_dec(v_h__3_670_);
v_k_685_ = lean_ctor_get(v_p_u2081_666_, 0);
lean_inc(v_k_685_);
v_v_686_ = lean_ctor_get(v_p_u2081_666_, 1);
lean_inc(v_v_686_);
v_p_687_ = lean_ctor_get(v_p_u2081_666_, 2);
lean_inc_ref(v_p_687_);
lean_dec_ref(v_p_u2081_666_);
v_k_688_ = lean_ctor_get(v_p_u2082_667_, 0);
lean_inc(v_k_688_);
v_v_689_ = lean_ctor_get(v_p_u2082_667_, 1);
lean_inc(v_v_689_);
v_p_690_ = lean_ctor_get(v_p_u2082_667_, 2);
lean_inc_ref(v_p_690_);
lean_dec_ref(v_p_u2082_667_);
v___x_691_ = lean_apply_6(v_h__4_671_, v_k_685_, v_v_686_, v_p_687_, v_k_688_, v_v_689_, v_p_690_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter(lean_object* v_motive_692_, lean_object* v_p_u2081_693_, lean_object* v_p_u2082_694_, lean_object* v_h__1_695_, lean_object* v_h__2_696_, lean_object* v_h__3_697_, lean_object* v_h__4_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(v_p_u2081_693_, v_p_u2082_694_, v_h__1_695_, v_h__2_696_, v_h__3_697_, v_h__4_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(lean_object* v_x_700_, lean_object* v_h__1_701_, lean_object* v_h__2_702_, lean_object* v_h__3_703_, lean_object* v_h__4_704_, lean_object* v_h__5_705_, lean_object* v_h__6_706_, lean_object* v_h__7_707_){
_start:
{
switch(lean_obj_tag(v_x_700_))
{
case 0:
{
lean_object* v_v_708_; lean_object* v___x_709_; 
lean_dec(v_h__7_707_);
lean_dec(v_h__6_706_);
lean_dec(v_h__5_705_);
lean_dec(v_h__3_703_);
lean_dec(v_h__2_702_);
lean_dec(v_h__1_701_);
v_v_708_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_v_708_);
lean_dec_ref(v_x_700_);
v___x_709_ = lean_apply_1(v_h__4_704_, v_v_708_);
return v___x_709_;
}
case 1:
{
lean_object* v_i_710_; lean_object* v___x_711_; 
lean_dec(v_h__7_707_);
lean_dec(v_h__6_706_);
lean_dec(v_h__4_704_);
lean_dec(v_h__3_703_);
lean_dec(v_h__2_702_);
lean_dec(v_h__1_701_);
v_i_710_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_i_710_);
lean_dec_ref(v_x_700_);
v___x_711_ = lean_apply_1(v_h__5_705_, v_i_710_);
return v___x_711_;
}
case 2:
{
lean_object* v_a_712_; lean_object* v_b_713_; lean_object* v___x_714_; 
lean_dec(v_h__7_707_);
lean_dec(v_h__6_706_);
lean_dec(v_h__5_705_);
lean_dec(v_h__4_704_);
lean_dec(v_h__3_703_);
lean_dec(v_h__2_702_);
v_a_712_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_a_712_);
v_b_713_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_b_713_);
lean_dec_ref(v_x_700_);
v___x_714_ = lean_apply_2(v_h__1_701_, v_a_712_, v_b_713_);
return v___x_714_;
}
case 3:
{
lean_object* v_a_715_; lean_object* v_b_716_; lean_object* v___x_717_; 
lean_dec(v_h__7_707_);
lean_dec(v_h__6_706_);
lean_dec(v_h__5_705_);
lean_dec(v_h__4_704_);
lean_dec(v_h__3_703_);
lean_dec(v_h__1_701_);
v_a_715_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_a_715_);
v_b_716_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_b_716_);
lean_dec_ref(v_x_700_);
v___x_717_ = lean_apply_2(v_h__2_702_, v_a_715_, v_b_716_);
return v___x_717_;
}
case 4:
{
lean_object* v_a_718_; lean_object* v___x_719_; 
lean_dec(v_h__7_707_);
lean_dec(v_h__6_706_);
lean_dec(v_h__5_705_);
lean_dec(v_h__4_704_);
lean_dec(v_h__2_702_);
lean_dec(v_h__1_701_);
v_a_718_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_a_718_);
lean_dec_ref(v_x_700_);
v___x_719_ = lean_apply_1(v_h__3_703_, v_a_718_);
return v___x_719_;
}
case 5:
{
lean_object* v_k_720_; lean_object* v_a_721_; lean_object* v___x_722_; 
lean_dec(v_h__7_707_);
lean_dec(v_h__5_705_);
lean_dec(v_h__4_704_);
lean_dec(v_h__3_703_);
lean_dec(v_h__2_702_);
lean_dec(v_h__1_701_);
v_k_720_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_k_720_);
v_a_721_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_a_721_);
lean_dec_ref(v_x_700_);
v___x_722_ = lean_apply_2(v_h__6_706_, v_k_720_, v_a_721_);
return v___x_722_;
}
default: 
{
lean_object* v_a_723_; lean_object* v_k_724_; lean_object* v___x_725_; 
lean_dec(v_h__6_706_);
lean_dec(v_h__5_705_);
lean_dec(v_h__4_704_);
lean_dec(v_h__3_703_);
lean_dec(v_h__2_702_);
lean_dec(v_h__1_701_);
v_a_723_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_a_723_);
v_k_724_ = lean_ctor_get(v_x_700_, 1);
lean_inc(v_k_724_);
lean_dec_ref(v_x_700_);
v___x_725_ = lean_apply_2(v_h__7_707_, v_a_723_, v_k_724_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter(lean_object* v_motive_726_, lean_object* v_x_727_, lean_object* v_h__1_728_, lean_object* v_h__2_729_, lean_object* v_h__3_730_, lean_object* v_h__4_731_, lean_object* v_h__5_732_, lean_object* v_h__6_733_, lean_object* v_h__7_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(v_x_727_, v_h__1_728_, v_h__2_729_, v_h__3_730_, v_h__4_731_, v_h__5_732_, v_h__6_733_, v_h__7_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* v_x_736_, lean_object* v_h__1_737_, lean_object* v_h__2_738_, lean_object* v_h__3_739_, lean_object* v_h__4_740_, lean_object* v_h__5_741_, lean_object* v_h__6_742_, lean_object* v_h__7_743_){
_start:
{
switch(lean_obj_tag(v_x_736_))
{
case 0:
{
lean_object* v_v_744_; lean_object* v___x_745_; 
lean_dec(v_h__7_743_);
lean_dec(v_h__6_742_);
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
v_v_744_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_v_744_);
lean_dec_ref(v_x_736_);
v___x_745_ = lean_apply_1(v_h__1_737_, v_v_744_);
return v___x_745_;
}
case 1:
{
lean_object* v_i_746_; lean_object* v___x_747_; 
lean_dec(v_h__7_743_);
lean_dec(v_h__6_742_);
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__3_739_);
lean_dec(v_h__1_737_);
v_i_746_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_i_746_);
lean_dec_ref(v_x_736_);
v___x_747_ = lean_apply_1(v_h__2_738_, v_i_746_);
return v___x_747_;
}
case 2:
{
lean_object* v_a_748_; lean_object* v_b_749_; lean_object* v___x_750_; 
lean_dec(v_h__7_743_);
lean_dec(v_h__6_742_);
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__2_738_);
lean_dec(v_h__1_737_);
v_a_748_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_a_748_);
v_b_749_ = lean_ctor_get(v_x_736_, 1);
lean_inc_ref(v_b_749_);
lean_dec_ref(v_x_736_);
v___x_750_ = lean_apply_2(v_h__3_739_, v_a_748_, v_b_749_);
return v___x_750_;
}
case 3:
{
lean_object* v_a_751_; lean_object* v_b_752_; lean_object* v___x_753_; 
lean_dec(v_h__7_743_);
lean_dec(v_h__6_742_);
lean_dec(v_h__5_741_);
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
lean_dec(v_h__1_737_);
v_a_751_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_a_751_);
v_b_752_ = lean_ctor_get(v_x_736_, 1);
lean_inc_ref(v_b_752_);
lean_dec_ref(v_x_736_);
v___x_753_ = lean_apply_2(v_h__4_740_, v_a_751_, v_b_752_);
return v___x_753_;
}
case 4:
{
lean_object* v_a_754_; lean_object* v___x_755_; 
lean_dec(v_h__6_742_);
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
lean_dec(v_h__1_737_);
v_a_754_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_a_754_);
lean_dec_ref(v_x_736_);
v___x_755_ = lean_apply_1(v_h__7_743_, v_a_754_);
return v___x_755_;
}
case 5:
{
lean_object* v_k_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
lean_dec(v_h__7_743_);
lean_dec(v_h__6_742_);
lean_dec(v_h__4_740_);
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
lean_dec(v_h__1_737_);
v_k_756_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_k_756_);
v_a_757_ = lean_ctor_get(v_x_736_, 1);
lean_inc_ref(v_a_757_);
lean_dec_ref(v_x_736_);
v___x_758_ = lean_apply_2(v_h__5_741_, v_k_756_, v_a_757_);
return v___x_758_;
}
default: 
{
lean_object* v_a_759_; lean_object* v_k_760_; lean_object* v___x_761_; 
lean_dec(v_h__7_743_);
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
lean_dec(v_h__1_737_);
v_a_759_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_a_759_);
v_k_760_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_k_760_);
lean_dec_ref(v_x_736_);
v___x_761_ = lean_apply_2(v_h__6_742_, v_a_759_, v_k_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* v_motive_762_, lean_object* v_x_763_, lean_object* v_h__1_764_, lean_object* v_h__2_765_, lean_object* v_h__3_766_, lean_object* v_h__4_767_, lean_object* v_h__5_768_, lean_object* v_h__6_769_, lean_object* v_h__7_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(v_x_763_, v_h__1_764_, v_h__2_765_, v_h__3_766_, v_h__4_767_, v_h__5_768_, v_h__6_769_, v_h__7_770_);
return v___x_771_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object* v_p_772_){
_start:
{
if (lean_obj_tag(v_p_772_) == 0)
{
lean_object* v_k_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_k_773_ = lean_ctor_get(v_p_772_, 0);
v___x_774_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_775_ = lean_int_dec_eq(v_k_773_, v___x_774_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; 
v___x_776_ = 1;
return v___x_776_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
}
else
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatEq___boxed(lean_object* v_p_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Int_Linear_Poly_isUnsatEq(v_p_779_);
lean_dec_ref(v_p_779_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidEq(lean_object* v_p_782_){
_start:
{
if (lean_obj_tag(v_p_782_) == 0)
{
lean_object* v_k_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_k_783_ = lean_ctor_get(v_p_782_, 0);
v___x_784_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_785_ = lean_int_dec_eq(v_k_783_, v___x_784_);
return v___x_785_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidEq___boxed(lean_object* v_p_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Int_Linear_Poly_isValidEq(v_p_787_);
lean_dec_ref(v_p_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* v_p_790_, lean_object* v_h__1_791_, lean_object* v_h__2_792_){
_start:
{
if (lean_obj_tag(v_p_790_) == 0)
{
lean_object* v_k_793_; lean_object* v___x_794_; 
lean_dec(v_h__2_792_);
v_k_793_ = lean_ctor_get(v_p_790_, 0);
lean_inc(v_k_793_);
lean_dec_ref(v_p_790_);
v___x_794_ = lean_apply_1(v_h__1_791_, v_k_793_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; 
lean_dec(v_h__1_791_);
v___x_795_ = lean_apply_2(v_h__2_792_, v_p_790_, lean_box(0));
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* v_motive_796_, lean_object* v_p_797_, lean_object* v_h__1_798_, lean_object* v_h__2_799_){
_start:
{
if (lean_obj_tag(v_p_797_) == 0)
{
lean_object* v_k_800_; lean_object* v___x_801_; 
lean_dec(v_h__2_799_);
v_k_800_ = lean_ctor_get(v_p_797_, 0);
lean_inc(v_k_800_);
lean_dec_ref(v_p_797_);
v___x_801_ = lean_apply_1(v_h__1_798_, v_k_800_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; 
lean_dec(v_h__1_798_);
v___x_802_ = lean_apply_2(v_h__2_799_, v_p_797_, lean_box(0));
return v___x_802_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object* v_p_803_){
_start:
{
if (lean_obj_tag(v_p_803_) == 0)
{
lean_object* v_k_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_k_804_ = lean_ctor_get(v_p_803_, 0);
v___x_805_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_806_ = lean_int_dec_lt(v___x_805_, v_k_804_);
return v___x_806_;
}
else
{
uint8_t v___x_807_; 
v___x_807_ = 0;
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatLe___boxed(lean_object* v_p_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Int_Linear_Poly_isUnsatLe(v_p_808_);
lean_dec_ref(v_p_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidLe(lean_object* v_p_811_){
_start:
{
if (lean_obj_tag(v_p_811_) == 0)
{
lean_object* v_k_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_k_812_ = lean_ctor_get(v_p_811_, 0);
v___x_813_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_814_ = lean_int_dec_le(v_k_812_, v___x_813_);
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidLe___boxed(lean_object* v_p_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Int_Linear_Poly_isValidLe(v_p_816_);
lean_dec_ref(v_p_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(lean_object* v_a_819_, lean_object* v_b_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = l_Int_gcd(v_a_819_, v_b_820_);
v___x_822_ = lean_nat_to_int(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd___boxed(lean_object* v_a_823_, lean_object* v_b_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(v_a_823_, v_b_824_);
lean_dec(v_b_824_);
lean_dec(v_a_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_826_) == 0)
{
return v_x_827_;
}
else
{
lean_object* v_k_828_; lean_object* v_p_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_k_828_ = lean_ctor_get(v_x_826_, 0);
v_p_829_ = lean_ctor_get(v_x_826_, 2);
v___x_830_ = l_Int_gcd(v_k_828_, v_x_827_);
lean_dec(v_x_827_);
v___x_831_ = lean_nat_to_int(v___x_830_);
v_x_826_ = v_p_829_;
v_x_827_ = v___x_831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs___boxed(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Int_Linear_Poly_gcdCoeffs(v_x_833_, v_x_834_);
lean_dec_ref(v_x_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_h__1_838_, lean_object* v_h__2_839_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
lean_object* v_k_840_; lean_object* v___x_841_; 
lean_dec(v_h__2_839_);
v_k_840_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_k_840_);
lean_dec_ref(v_x_836_);
v___x_841_ = lean_apply_2(v_h__1_838_, v_k_840_, v_x_837_);
return v___x_841_;
}
else
{
lean_object* v_k_842_; lean_object* v_v_843_; lean_object* v_p_844_; lean_object* v___x_845_; 
lean_dec(v_h__1_838_);
v_k_842_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_k_842_);
v_v_843_ = lean_ctor_get(v_x_836_, 1);
lean_inc(v_v_843_);
v_p_844_ = lean_ctor_get(v_x_836_, 2);
lean_inc_ref(v_p_844_);
lean_dec_ref(v_x_836_);
v___x_845_ = lean_apply_4(v_h__2_839_, v_k_842_, v_v_843_, v_p_844_, v_x_837_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object* v_motive_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_h__1_849_, lean_object* v_h__2_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(v_x_847_, v_x_848_, v_h__1_849_, v_h__2_850_);
return v___x_851_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object* v_k_852_, lean_object* v_p_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_854_ = l_Int_Linear_Poly_getConst(v_p_853_);
v___x_855_ = l_Int_Linear_Poly_gcdCoeffs(v_p_853_, v_k_852_);
v___x_856_ = lean_int_emod(v___x_854_, v___x_855_);
lean_dec(v___x_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_858_ = lean_int_dec_eq(v___x_856_, v___x_857_);
lean_dec(v___x_856_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = 1;
return v___x_859_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = 0;
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDvd___boxed(lean_object* v_k_861_, lean_object* v_p_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l_Int_Linear_Poly_isUnsatDvd(v_k_861_, v_p_862_);
lean_dec_ref(v_p_862_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object* v_p_u2081_865_, lean_object* v_p_u2082_866_, lean_object* v_h__1_867_, lean_object* v_h__2_868_){
_start:
{
if (lean_obj_tag(v_p_u2081_865_) == 1)
{
if (lean_obj_tag(v_p_u2082_866_) == 1)
{
lean_object* v_k_869_; lean_object* v_v_870_; lean_object* v_p_871_; lean_object* v_k_872_; lean_object* v_v_873_; lean_object* v_p_874_; lean_object* v___x_875_; 
lean_dec(v_h__2_868_);
v_k_869_ = lean_ctor_get(v_p_u2081_865_, 0);
lean_inc(v_k_869_);
v_v_870_ = lean_ctor_get(v_p_u2081_865_, 1);
lean_inc(v_v_870_);
v_p_871_ = lean_ctor_get(v_p_u2081_865_, 2);
lean_inc_ref(v_p_871_);
lean_dec_ref(v_p_u2081_865_);
v_k_872_ = lean_ctor_get(v_p_u2082_866_, 0);
lean_inc(v_k_872_);
v_v_873_ = lean_ctor_get(v_p_u2082_866_, 1);
lean_inc(v_v_873_);
v_p_874_ = lean_ctor_get(v_p_u2082_866_, 2);
lean_inc_ref(v_p_874_);
lean_dec_ref(v_p_u2082_866_);
v___x_875_ = lean_apply_6(v_h__1_867_, v_k_869_, v_v_870_, v_p_871_, v_k_872_, v_v_873_, v_p_874_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; 
lean_dec(v_h__1_867_);
v___x_876_ = lean_apply_3(v_h__2_868_, v_p_u2081_865_, v_p_u2082_866_, lean_box(0));
return v___x_876_;
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v_h__1_867_);
v___x_877_ = lean_apply_3(v_h__2_868_, v_p_u2081_865_, v_p_u2082_866_, lean_box(0));
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object* v_motive_878_, lean_object* v_p_u2081_879_, lean_object* v_p_u2082_880_, lean_object* v_h__1_881_, lean_object* v_h__2_882_){
_start:
{
if (lean_obj_tag(v_p_u2081_879_) == 1)
{
if (lean_obj_tag(v_p_u2082_880_) == 1)
{
lean_object* v_k_883_; lean_object* v_v_884_; lean_object* v_p_885_; lean_object* v_k_886_; lean_object* v_v_887_; lean_object* v_p_888_; lean_object* v___x_889_; 
lean_dec(v_h__2_882_);
v_k_883_ = lean_ctor_get(v_p_u2081_879_, 0);
lean_inc(v_k_883_);
v_v_884_ = lean_ctor_get(v_p_u2081_879_, 1);
lean_inc(v_v_884_);
v_p_885_ = lean_ctor_get(v_p_u2081_879_, 2);
lean_inc_ref(v_p_885_);
lean_dec_ref(v_p_u2081_879_);
v_k_886_ = lean_ctor_get(v_p_u2082_880_, 0);
lean_inc(v_k_886_);
v_v_887_ = lean_ctor_get(v_p_u2082_880_, 1);
lean_inc(v_v_887_);
v_p_888_ = lean_ctor_get(v_p_u2082_880_, 2);
lean_inc_ref(v_p_888_);
lean_dec_ref(v_p_u2082_880_);
v___x_889_ = lean_apply_6(v_h__1_881_, v_k_883_, v_v_884_, v_p_885_, v_k_886_, v_v_887_, v_p_888_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; 
lean_dec(v_h__1_881_);
v___x_890_ = lean_apply_3(v_h__2_882_, v_p_u2081_879_, v_p_u2082_880_, lean_box(0));
return v___x_890_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec(v_h__1_881_);
v___x_891_ = lean_apply_3(v_h__2_882_, v_p_u2081_879_, v_p_u2082_880_, lean_box(0));
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff(lean_object* v_p_892_){
_start:
{
if (lean_obj_tag(v_p_892_) == 1)
{
lean_object* v_k_893_; 
v_k_893_ = lean_ctor_get(v_p_892_, 0);
lean_inc(v_k_893_);
return v_k_893_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff___boxed(lean_object* v_p_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Int_Linear_Poly_leadCoeff(v_p_895_);
lean_dec_ref(v_p_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff(lean_object* v_p_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_p_897_) == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
return v___x_899_;
}
else
{
lean_object* v_k_900_; lean_object* v_v_901_; lean_object* v_p_902_; uint8_t v___x_903_; 
v_k_900_ = lean_ctor_get(v_p_897_, 0);
v_v_901_ = lean_ctor_get(v_p_897_, 1);
v_p_902_ = lean_ctor_get(v_p_897_, 2);
v___x_903_ = lean_nat_dec_eq(v_x_898_, v_v_901_);
if (v___x_903_ == 0)
{
v_p_897_ = v_p_902_;
goto _start;
}
else
{
lean_inc(v_k_900_);
return v_k_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff___boxed(lean_object* v_p_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Int_Linear_Poly_coeff(v_p_905_, v_x_906_);
lean_dec(v_x_906_);
lean_dec_ref(v_p_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter___redArg(lean_object* v_p_908_, lean_object* v_h__1_909_, lean_object* v_h__2_910_){
_start:
{
if (lean_obj_tag(v_p_908_) == 0)
{
lean_object* v_k_911_; lean_object* v___x_912_; 
lean_dec(v_h__1_909_);
v_k_911_ = lean_ctor_get(v_p_908_, 0);
lean_inc(v_k_911_);
lean_dec_ref(v_p_908_);
v___x_912_ = lean_apply_1(v_h__2_910_, v_k_911_);
return v___x_912_;
}
else
{
lean_object* v_k_913_; lean_object* v_v_914_; lean_object* v_p_915_; lean_object* v___x_916_; 
lean_dec(v_h__2_910_);
v_k_913_ = lean_ctor_get(v_p_908_, 0);
lean_inc(v_k_913_);
v_v_914_ = lean_ctor_get(v_p_908_, 1);
lean_inc(v_v_914_);
v_p_915_ = lean_ctor_get(v_p_908_, 2);
lean_inc_ref(v_p_915_);
lean_dec_ref(v_p_908_);
v___x_916_ = lean_apply_3(v_h__1_909_, v_k_913_, v_v_914_, v_p_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter(lean_object* v_motive_917_, lean_object* v_p_918_, lean_object* v_h__1_919_, lean_object* v_h__2_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter___redArg(v_p_918_, v_h__1_919_, v_h__2_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_abs(lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_nat_abs(v_x_922_);
v___x_924_ = lean_nat_to_int(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_abs___boxed(lean_object* v_x_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Int_Linear_abs(v_x_925_);
lean_dec(v_x_925_);
return v_res_926_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDiseq(lean_object* v_p_927_){
_start:
{
if (lean_obj_tag(v_p_927_) == 0)
{
lean_object* v_k_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_k_928_ = lean_ctor_get(v_p_927_, 0);
v___x_929_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_930_ = lean_int_dec_eq(v_k_928_, v___x_929_);
return v___x_930_;
}
else
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDiseq___boxed(lean_object* v_p_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Int_Linear_Poly_isUnsatDiseq(v_p_932_);
lean_dec_ref(v_p_932_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail(lean_object* v_p_935_){
_start:
{
if (lean_obj_tag(v_p_935_) == 1)
{
lean_object* v_p_936_; 
v_p_936_ = lean_ctor_get(v_p_935_, 2);
lean_inc_ref(v_p_936_);
return v_p_936_;
}
else
{
lean_inc_ref(v_p_935_);
return v_p_935_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail___boxed(lean_object* v_p_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Int_Linear_Poly_tail(v_p_937_);
lean_dec_ref(v_p_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object* v_p_939_, lean_object* v_h__1_940_, lean_object* v_h__2_941_){
_start:
{
if (lean_obj_tag(v_p_939_) == 1)
{
lean_object* v_k_942_; lean_object* v_v_943_; lean_object* v_p_944_; lean_object* v___x_945_; 
lean_dec(v_h__2_941_);
v_k_942_ = lean_ctor_get(v_p_939_, 0);
lean_inc(v_k_942_);
v_v_943_ = lean_ctor_get(v_p_939_, 1);
lean_inc(v_v_943_);
v_p_944_ = lean_ctor_get(v_p_939_, 2);
lean_inc_ref(v_p_944_);
lean_dec_ref(v_p_939_);
v___x_945_ = lean_apply_3(v_h__1_940_, v_k_942_, v_v_943_, v_p_944_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
lean_dec(v_h__1_940_);
v___x_946_ = lean_apply_2(v_h__2_941_, v_p_939_, lean_box(0));
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter(lean_object* v_motive_947_, lean_object* v_p_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_){
_start:
{
if (lean_obj_tag(v_p_948_) == 1)
{
lean_object* v_k_951_; lean_object* v_v_952_; lean_object* v_p_953_; lean_object* v___x_954_; 
lean_dec(v_h__2_950_);
v_k_951_ = lean_ctor_get(v_p_948_, 0);
lean_inc(v_k_951_);
v_v_952_ = lean_ctor_get(v_p_948_, 1);
lean_inc(v_v_952_);
v_p_953_ = lean_ctor_get(v_p_948_, 2);
lean_inc_ref(v_p_953_);
lean_dec_ref(v_p_948_);
v___x_954_ = lean_apply_3(v_h__1_949_, v_k_951_, v_v_952_, v_p_953_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; 
lean_dec(v_h__1_949_);
v___x_955_ = lean_apply_2(v_h__2_950_, v_p_948_, lean_box(0));
return v___x_955_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnAdd(lean_object* v_p_956_, lean_object* v_k_957_){
_start:
{
if (lean_obj_tag(v_p_956_) == 0)
{
uint8_t v___x_958_; 
lean_dec_ref(v_p_956_);
lean_dec_ref(v_k_957_);
v___x_958_ = 0;
return v___x_958_;
}
else
{
lean_object* v_a_959_; lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_a_959_ = lean_ctor_get(v_p_956_, 0);
lean_inc(v_a_959_);
v_a_960_ = lean_ctor_get(v_p_956_, 1);
lean_inc(v_a_960_);
v_a_961_ = lean_ctor_get(v_p_956_, 2);
lean_inc_ref(v_a_961_);
lean_dec_ref(v_p_956_);
v___x_962_ = lean_apply_3(v_k_957_, v_a_959_, v_a_960_, v_a_961_);
v___x_963_ = lean_unbox(v___x_962_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnAdd___boxed(lean_object* v_p_964_, lean_object* v_k_965_){
_start:
{
uint8_t v_res_966_; lean_object* v_r_967_; 
v_res_966_ = l_Int_Linear_Poly_casesOnAdd(v_p_964_, v_k_965_);
v_r_967_ = lean_box(v_res_966_);
return v_r_967_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnNum(lean_object* v_p_968_, lean_object* v_k_969_){
_start:
{
if (lean_obj_tag(v_p_968_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_a_970_ = lean_ctor_get(v_p_968_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v_p_968_);
v___x_971_ = lean_apply_1(v_k_969_, v_a_970_);
v___x_972_ = lean_unbox(v___x_971_);
return v___x_972_;
}
else
{
uint8_t v___x_973_; 
lean_dec_ref(v_p_968_);
lean_dec_ref(v_k_969_);
v___x_973_ = 0;
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnNum___boxed(lean_object* v_p_974_, lean_object* v_k_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Int_Linear_Poly_casesOnNum(v_p_974_, v_k_975_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_emod__le__cert(lean_object* v_y_978_, lean_object* v_n_979_){
_start:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_981_ = lean_int_dec_eq(v_y_978_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_982_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
v___x_983_ = lean_nat_abs(v_y_978_);
v___x_984_ = lean_nat_to_int(v___x_983_);
v___x_985_ = lean_int_sub(v___x_982_, v___x_984_);
lean_dec(v___x_984_);
v___x_986_ = lean_int_dec_eq(v_n_979_, v___x_985_);
lean_dec(v___x_985_);
return v___x_986_;
}
else
{
uint8_t v___x_987_; 
v___x_987_ = 0;
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_emod__le__cert___boxed(lean_object* v_y_988_, lean_object* v_n_989_){
_start:
{
uint8_t v_res_990_; lean_object* v_r_991_; 
v_res_990_ = l_Int_Linear_emod__le__cert(v_y_988_, v_n_989_);
lean_dec(v_n_989_);
lean_dec(v_y_988_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__cert(lean_object* v_p_u2081_992_, lean_object* v_p_u2082_993_){
_start:
{
if (lean_obj_tag(v_p_u2081_992_) == 0)
{
if (lean_obj_tag(v_p_u2082_993_) == 0)
{
lean_object* v_k_994_; lean_object* v_k_995_; uint8_t v___x_996_; 
v_k_994_ = lean_ctor_get(v_p_u2081_992_, 0);
v_k_995_ = lean_ctor_get(v_p_u2082_993_, 0);
v___x_996_ = lean_int_dec_le(v_k_995_, v_k_994_);
return v___x_996_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_993_) == 0)
{
uint8_t v___x_998_; 
v___x_998_ = 0;
return v___x_998_;
}
else
{
lean_object* v_k_999_; lean_object* v_v_1000_; lean_object* v_p_1001_; lean_object* v_k_1002_; lean_object* v_v_1003_; lean_object* v_p_1004_; uint8_t v___y_1006_; uint8_t v___x_1008_; 
v_k_999_ = lean_ctor_get(v_p_u2081_992_, 0);
v_v_1000_ = lean_ctor_get(v_p_u2081_992_, 1);
v_p_1001_ = lean_ctor_get(v_p_u2081_992_, 2);
v_k_1002_ = lean_ctor_get(v_p_u2082_993_, 0);
v_v_1003_ = lean_ctor_get(v_p_u2082_993_, 1);
v_p_1004_ = lean_ctor_get(v_p_u2082_993_, 2);
v___x_1008_ = lean_int_dec_eq(v_k_999_, v_k_1002_);
if (v___x_1008_ == 0)
{
v___y_1006_ = v___x_1008_;
goto v___jp_1005_;
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_eq(v_v_1000_, v_v_1003_);
v___y_1006_ = v___x_1009_;
goto v___jp_1005_;
}
v___jp_1005_:
{
if (v___y_1006_ == 0)
{
return v___y_1006_;
}
else
{
v_p_u2081_992_ = v_p_1001_;
v_p_u2082_993_ = v_p_1004_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__cert___boxed(lean_object* v_p_u2081_1010_, lean_object* v_p_u2082_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Int_Linear_le__of__le__cert(v_p_u2081_1010_, v_p_u2082_1011_);
lean_dec_ref(v_p_u2082_1011_);
lean_dec_ref(v_p_u2081_1010_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object* v_p_u2081_1014_, lean_object* v_p_u2082_1015_, lean_object* v_h__1_1016_, lean_object* v_h__2_1017_, lean_object* v_h__3_1018_, lean_object* v_h__4_1019_){
_start:
{
if (lean_obj_tag(v_p_u2081_1014_) == 0)
{
lean_dec(v_h__4_1019_);
lean_dec(v_h__1_1016_);
if (lean_obj_tag(v_p_u2082_1015_) == 0)
{
lean_object* v_k_1020_; lean_object* v_k_1021_; lean_object* v___x_1022_; 
lean_dec(v_h__2_1017_);
v_k_1020_ = lean_ctor_get(v_p_u2081_1014_, 0);
lean_inc(v_k_1020_);
lean_dec_ref(v_p_u2081_1014_);
v_k_1021_ = lean_ctor_get(v_p_u2082_1015_, 0);
lean_inc(v_k_1021_);
lean_dec_ref(v_p_u2082_1015_);
v___x_1022_ = lean_apply_2(v_h__3_1018_, v_k_1020_, v_k_1021_);
return v___x_1022_;
}
else
{
lean_object* v_k_1023_; lean_object* v_k_1024_; lean_object* v_v_1025_; lean_object* v_p_1026_; lean_object* v___x_1027_; 
lean_dec(v_h__3_1018_);
v_k_1023_ = lean_ctor_get(v_p_u2081_1014_, 0);
lean_inc(v_k_1023_);
lean_dec_ref(v_p_u2081_1014_);
v_k_1024_ = lean_ctor_get(v_p_u2082_1015_, 0);
lean_inc(v_k_1024_);
v_v_1025_ = lean_ctor_get(v_p_u2082_1015_, 1);
lean_inc(v_v_1025_);
v_p_1026_ = lean_ctor_get(v_p_u2082_1015_, 2);
lean_inc_ref(v_p_1026_);
lean_dec_ref(v_p_u2082_1015_);
v___x_1027_ = lean_apply_4(v_h__2_1017_, v_k_1023_, v_k_1024_, v_v_1025_, v_p_1026_);
return v___x_1027_;
}
}
else
{
lean_dec(v_h__3_1018_);
lean_dec(v_h__2_1017_);
if (lean_obj_tag(v_p_u2082_1015_) == 0)
{
lean_object* v_k_1028_; lean_object* v_v_1029_; lean_object* v_p_1030_; lean_object* v_k_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__4_1019_);
v_k_1028_ = lean_ctor_get(v_p_u2081_1014_, 0);
lean_inc(v_k_1028_);
v_v_1029_ = lean_ctor_get(v_p_u2081_1014_, 1);
lean_inc(v_v_1029_);
v_p_1030_ = lean_ctor_get(v_p_u2081_1014_, 2);
lean_inc_ref(v_p_1030_);
lean_dec_ref(v_p_u2081_1014_);
v_k_1031_ = lean_ctor_get(v_p_u2082_1015_, 0);
lean_inc(v_k_1031_);
lean_dec_ref(v_p_u2082_1015_);
v___x_1032_ = lean_apply_4(v_h__1_1016_, v_k_1028_, v_v_1029_, v_p_1030_, v_k_1031_);
return v___x_1032_;
}
else
{
lean_object* v_k_1033_; lean_object* v_v_1034_; lean_object* v_p_1035_; lean_object* v_k_1036_; lean_object* v_v_1037_; lean_object* v_p_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__1_1016_);
v_k_1033_ = lean_ctor_get(v_p_u2081_1014_, 0);
lean_inc(v_k_1033_);
v_v_1034_ = lean_ctor_get(v_p_u2081_1014_, 1);
lean_inc(v_v_1034_);
v_p_1035_ = lean_ctor_get(v_p_u2081_1014_, 2);
lean_inc_ref(v_p_1035_);
lean_dec_ref(v_p_u2081_1014_);
v_k_1036_ = lean_ctor_get(v_p_u2082_1015_, 0);
lean_inc(v_k_1036_);
v_v_1037_ = lean_ctor_get(v_p_u2082_1015_, 1);
lean_inc(v_v_1037_);
v_p_1038_ = lean_ctor_get(v_p_u2082_1015_, 2);
lean_inc_ref(v_p_1038_);
lean_dec_ref(v_p_u2082_1015_);
v___x_1039_ = lean_apply_6(v_h__4_1019_, v_k_1033_, v_v_1034_, v_p_1035_, v_k_1036_, v_v_1037_, v_p_1038_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter(lean_object* v_motive_1040_, lean_object* v_p_u2081_1041_, lean_object* v_p_u2082_1042_, lean_object* v_h__1_1043_, lean_object* v_h__2_1044_, lean_object* v_h__3_1045_, lean_object* v_h__4_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter___redArg(v_p_u2081_1041_, v_p_u2082_1042_, v_h__1_1043_, v_h__2_1044_, v_h__3_1045_, v_h__4_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_not__le__of__le__cert(lean_object* v_p_u2081_1048_, lean_object* v_p_u2082_1049_){
_start:
{
if (lean_obj_tag(v_p_u2081_1048_) == 0)
{
if (lean_obj_tag(v_p_u2082_1049_) == 0)
{
lean_object* v_k_1050_; lean_object* v_k_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_k_1050_ = lean_ctor_get(v_p_u2081_1048_, 0);
v_k_1051_ = lean_ctor_get(v_p_u2082_1049_, 0);
v___x_1052_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
v___x_1053_ = lean_int_sub(v___x_1052_, v_k_1051_);
v___x_1054_ = lean_int_dec_le(v___x_1053_, v_k_1050_);
lean_dec(v___x_1053_);
return v___x_1054_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = 0;
return v___x_1055_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1049_) == 0)
{
uint8_t v___x_1056_; 
v___x_1056_ = 0;
return v___x_1056_;
}
else
{
lean_object* v_k_1057_; lean_object* v_v_1058_; lean_object* v_p_1059_; lean_object* v_k_1060_; lean_object* v_v_1061_; lean_object* v_p_1062_; uint8_t v___y_1064_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_k_1057_ = lean_ctor_get(v_p_u2081_1048_, 0);
v_v_1058_ = lean_ctor_get(v_p_u2081_1048_, 1);
v_p_1059_ = lean_ctor_get(v_p_u2081_1048_, 2);
v_k_1060_ = lean_ctor_get(v_p_u2082_1049_, 0);
v_v_1061_ = lean_ctor_get(v_p_u2082_1049_, 1);
v_p_1062_ = lean_ctor_get(v_p_u2082_1049_, 2);
v___x_1066_ = lean_int_neg(v_k_1060_);
v___x_1067_ = lean_int_dec_eq(v_k_1057_, v___x_1066_);
lean_dec(v___x_1066_);
if (v___x_1067_ == 0)
{
v___y_1064_ = v___x_1067_;
goto v___jp_1063_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_nat_dec_eq(v_v_1058_, v_v_1061_);
v___y_1064_ = v___x_1068_;
goto v___jp_1063_;
}
v___jp_1063_:
{
if (v___y_1064_ == 0)
{
return v___y_1064_;
}
else
{
v_p_u2081_1048_ = v_p_1059_;
v_p_u2082_1049_ = v_p_1062_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_not__le__of__le__cert___boxed(lean_object* v_p_u2081_1069_, lean_object* v_p_u2082_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Int_Linear_not__le__of__le__cert(v_p_u2081_1069_, v_p_u2082_1070_);
lean_dec_ref(v_p_u2082_1070_);
lean_dec_ref(v_p_u2081_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Linear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_Int_Linear_instInhabitedExpr_default = _init_l_Int_Linear_instInhabitedExpr_default();
lean_mark_persistent(l_Int_Linear_instInhabitedExpr_default);
l_Int_Linear_instInhabitedExpr = _init_l_Int_Linear_instInhabitedExpr();
lean_mark_persistent(l_Int_Linear_instInhabitedExpr);
l_Int_Linear_hugeFuel = _init_l_Int_Linear_hugeFuel();
lean_mark_persistent(l_Int_Linear_hugeFuel);
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
