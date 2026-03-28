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
if (lean_obj_tag(v_p_310_) == 0)
{
lean_object* v_k_313_; lean_object* v___x_314_; 
lean_dec(v_h__2_312_);
v_k_313_ = lean_ctor_get(v_p_310_, 0);
lean_inc(v_k_313_);
lean_dec_ref(v_p_310_);
v___x_314_ = lean_apply_1(v_h__1_311_, v_k_313_);
return v___x_314_;
}
else
{
lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v_p_317_; lean_object* v___x_318_; 
lean_dec(v_h__1_311_);
v_k_315_ = lean_ctor_get(v_p_310_, 0);
lean_inc(v_k_315_);
v_v_316_ = lean_ctor_get(v_p_310_, 1);
lean_inc(v_v_316_);
v_p_317_ = lean_ctor_get(v_p_310_, 2);
lean_inc_ref(v_p_317_);
lean_dec_ref(v_p_310_);
v___x_318_ = lean_apply_3(v_h__2_312_, v_k_315_, v_v_316_, v_p_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst(lean_object* v_p_319_, lean_object* v_k_320_){
_start:
{
if (lean_obj_tag(v_p_319_) == 0)
{
lean_object* v_k_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_k_321_ = lean_ctor_get(v_p_319_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_p_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v_p_319_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_k_321_);
lean_dec(v_p_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_int_add(v_k_320_, v_k_321_);
lean_dec(v_k_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_k_330_; lean_object* v_v_331_; lean_object* v_p_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_k_330_ = lean_ctor_get(v_p_319_, 0);
v_v_331_ = lean_ctor_get(v_p_319_, 1);
v_p_332_ = lean_ctor_get(v_p_319_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_p_319_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v_p_319_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_p_332_);
lean_inc(v_v_331_);
lean_inc(v_k_330_);
lean_dec(v_p_319_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = l_Int_Linear_Poly_addConst(v_p_332_, v_k_320_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 2, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_k_330_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_v_331_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_addConst___boxed(lean_object* v_p_341_, lean_object* v_k_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Int_Linear_Poly_addConst(v_p_341_, v_k_342_);
lean_dec(v_k_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_insert(lean_object* v_k_344_, lean_object* v_v_345_, lean_object* v_p_346_){
_start:
{
if (lean_obj_tag(v_p_346_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v_k_344_);
lean_ctor_set(v___x_347_, 1, v_v_345_);
lean_ctor_set(v___x_347_, 2, v_p_346_);
return v___x_347_;
}
else
{
lean_object* v_k_348_; lean_object* v_v_349_; lean_object* v_p_350_; uint8_t v___x_351_; 
v_k_348_ = lean_ctor_get(v_p_346_, 0);
v_v_349_ = lean_ctor_get(v_p_346_, 1);
v_p_350_ = lean_ctor_get(v_p_346_, 2);
v___x_351_ = l_Nat_blt(v_v_349_, v_v_345_);
if (v___x_351_ == 0)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_p_350_);
lean_inc(v_v_349_);
lean_inc(v_k_348_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_p_346_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_367_ = lean_ctor_get(v_p_346_, 2);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_p_346_, 1);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_p_346_, 0);
lean_dec(v_unused_369_);
v___x_353_ = v_p_346_;
v_isShared_354_ = v_isSharedCheck_366_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_p_346_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_366_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint8_t v___x_355_; 
v___x_355_ = lean_nat_dec_eq(v_v_345_, v_v_349_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = l_Int_Linear_Poly_insert(v_k_344_, v_v_345_, v_p_350_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 2, v___x_356_);
v___x_358_ = v___x_353_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_k_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_v_349_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
lean_dec(v_v_345_);
v___x_360_ = lean_int_add(v_k_344_, v_k_348_);
lean_dec(v_k_348_);
lean_dec(v_k_344_);
v___x_361_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_362_ = lean_int_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_364_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_360_);
v___x_364_ = v___x_353_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_v_349_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_p_350_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_dec(v___x_360_);
lean_del_object(v___x_353_);
lean_dec(v_v_349_);
return v_p_350_;
}
}
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_370_, 0, v_k_344_);
lean_ctor_set(v___x_370_, 1, v_v_345_);
lean_ctor_set(v___x_370_, 2, v_p_346_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_norm(lean_object* v_p_371_){
_start:
{
if (lean_obj_tag(v_p_371_) == 0)
{
return v_p_371_;
}
else
{
lean_object* v_k_372_; lean_object* v_v_373_; lean_object* v_p_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_k_372_ = lean_ctor_get(v_p_371_, 0);
lean_inc(v_k_372_);
v_v_373_ = lean_ctor_get(v_p_371_, 1);
lean_inc(v_v_373_);
v_p_374_ = lean_ctor_get(v_p_371_, 2);
lean_inc_ref(v_p_374_);
lean_dec_ref(v_p_371_);
v___x_375_ = l_Int_Linear_Poly_norm(v_p_374_);
v___x_376_ = l_Int_Linear_Poly_insert(v_k_372_, v_v_373_, v___x_375_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_append(lean_object* v_p_u2081_377_, lean_object* v_p_u2082_378_){
_start:
{
if (lean_obj_tag(v_p_u2081_377_) == 0)
{
lean_object* v_k_379_; lean_object* v___x_380_; 
v_k_379_ = lean_ctor_get(v_p_u2081_377_, 0);
lean_inc(v_k_379_);
lean_dec_ref(v_p_u2081_377_);
v___x_380_ = l_Int_Linear_Poly_addConst(v_p_u2082_378_, v_k_379_);
lean_dec(v_k_379_);
return v___x_380_;
}
else
{
lean_object* v_k_381_; lean_object* v_v_382_; lean_object* v_p_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
v_k_381_ = lean_ctor_get(v_p_u2081_377_, 0);
v_v_382_ = lean_ctor_get(v_p_u2081_377_, 1);
v_p_383_ = lean_ctor_get(v_p_u2081_377_, 2);
v_isSharedCheck_391_ = !lean_is_exclusive(v_p_u2081_377_);
if (v_isSharedCheck_391_ == 0)
{
v___x_385_ = v_p_u2081_377_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_p_383_);
lean_inc(v_v_382_);
lean_inc(v_k_381_);
lean_dec(v_p_u2081_377_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = l_Int_Linear_Poly_append(v_p_383_, v_p_u2082_378_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 2, v___x_387_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_k_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_v_382_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine_x27(lean_object* v_fuel_392_, lean_object* v_p_u2081_393_, lean_object* v_p_u2082_394_){
_start:
{
lean_object* v_zero_395_; uint8_t v_isZero_396_; 
v_zero_395_ = lean_unsigned_to_nat(0u);
v_isZero_396_ = lean_nat_dec_eq(v_fuel_392_, v_zero_395_);
if (v_isZero_396_ == 1)
{
lean_object* v___x_397_; 
lean_dec(v_fuel_392_);
v___x_397_ = l_Int_Linear_Poly_append(v_p_u2081_393_, v_p_u2082_394_);
return v___x_397_;
}
else
{
lean_object* v_one_398_; lean_object* v_n_399_; 
v_one_398_ = lean_unsigned_to_nat(1u);
v_n_399_ = lean_nat_sub(v_fuel_392_, v_one_398_);
lean_dec(v_fuel_392_);
if (lean_obj_tag(v_p_u2081_393_) == 0)
{
if (lean_obj_tag(v_p_u2082_394_) == 0)
{
lean_object* v_k_400_; lean_object* v_k_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_n_399_);
v_k_400_ = lean_ctor_get(v_p_u2081_393_, 0);
lean_inc(v_k_400_);
lean_dec_ref(v_p_u2081_393_);
v_k_401_ = lean_ctor_get(v_p_u2082_394_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_p_u2082_394_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v_p_u2082_394_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_k_401_);
lean_dec(v_p_u2082_394_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_int_add(v_k_400_, v_k_401_);
lean_dec(v_k_401_);
lean_dec(v_k_400_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_k_410_; lean_object* v_v_411_; lean_object* v_p_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_k_410_ = lean_ctor_get(v_p_u2082_394_, 0);
v_v_411_ = lean_ctor_get(v_p_u2082_394_, 1);
v_p_412_ = lean_ctor_get(v_p_u2082_394_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_p_u2082_394_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v_p_u2082_394_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_p_412_);
lean_inc(v_v_411_);
lean_inc(v_k_410_);
lean_dec(v_p_u2082_394_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = l_Int_Linear_Poly_combine_x27(v_n_399_, v_p_u2081_393_, v_p_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_k_410_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_v_411_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
if (lean_obj_tag(v_p_u2082_394_) == 0)
{
lean_object* v_k_421_; lean_object* v_v_422_; lean_object* v_p_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
v_k_421_ = lean_ctor_get(v_p_u2081_393_, 0);
v_v_422_ = lean_ctor_get(v_p_u2081_393_, 1);
v_p_423_ = lean_ctor_get(v_p_u2081_393_, 2);
v_isSharedCheck_431_ = !lean_is_exclusive(v_p_u2081_393_);
if (v_isSharedCheck_431_ == 0)
{
v___x_425_ = v_p_u2081_393_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_p_423_);
lean_inc(v_v_422_);
lean_inc(v_k_421_);
lean_dec(v_p_u2081_393_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Int_Linear_Poly_combine_x27(v_n_399_, v_p_423_, v_p_u2082_394_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 2, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_k_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_v_422_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_k_432_; lean_object* v_v_433_; lean_object* v_p_434_; lean_object* v_k_435_; lean_object* v_v_436_; lean_object* v_p_437_; uint8_t v___x_438_; 
v_k_432_ = lean_ctor_get(v_p_u2081_393_, 0);
v_v_433_ = lean_ctor_get(v_p_u2081_393_, 1);
v_p_434_ = lean_ctor_get(v_p_u2081_393_, 2);
v_k_435_ = lean_ctor_get(v_p_u2082_394_, 0);
v_v_436_ = lean_ctor_get(v_p_u2082_394_, 1);
v_p_437_ = lean_ctor_get(v_p_u2082_394_, 2);
v___x_438_ = lean_nat_dec_eq(v_v_433_, v_v_436_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; 
v___x_439_ = l_Nat_blt(v_v_436_, v_v_433_);
if (v___x_439_ == 0)
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
lean_inc_ref(v_p_437_);
lean_inc(v_v_436_);
lean_inc(v_k_435_);
v_isSharedCheck_447_ = !lean_is_exclusive(v_p_u2082_394_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_448_ = lean_ctor_get(v_p_u2082_394_, 2);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_p_u2082_394_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_p_u2082_394_, 0);
lean_dec(v_unused_450_);
v___x_441_ = v_p_u2082_394_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_p_u2082_394_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = l_Int_Linear_Poly_combine_x27(v_n_399_, v_p_u2081_393_, v_p_437_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 2, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_k_435_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_v_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
lean_inc_ref(v_p_434_);
lean_inc(v_v_433_);
lean_inc(v_k_432_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_p_u2081_393_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_459_ = lean_ctor_get(v_p_u2081_393_, 2);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_p_u2081_393_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_p_u2081_393_, 0);
lean_dec(v_unused_461_);
v___x_452_ = v_p_u2081_393_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_p_u2081_393_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = l_Int_Linear_Poly_combine_x27(v_n_399_, v_p_434_, v_p_u2082_394_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 2, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_k_432_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_v_433_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_473_; 
lean_inc_ref(v_p_437_);
lean_inc(v_k_435_);
lean_inc_ref(v_p_434_);
lean_inc(v_v_433_);
lean_inc(v_k_432_);
lean_dec_ref(v_p_u2081_393_);
v_isSharedCheck_473_ = !lean_is_exclusive(v_p_u2082_394_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_474_ = lean_ctor_get(v_p_u2082_394_, 2);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_p_u2082_394_, 1);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_p_u2082_394_, 0);
lean_dec(v_unused_476_);
v___x_463_ = v_p_u2082_394_;
v_isShared_464_ = v_isSharedCheck_473_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_p_u2082_394_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_473_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_a_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_a_465_ = lean_int_add(v_k_432_, v_k_435_);
lean_dec(v_k_435_);
lean_dec(v_k_432_);
v___x_466_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_467_ = lean_int_dec_eq(v_a_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = l_Int_Linear_Poly_combine_x27(v_n_399_, v_p_434_, v_p_437_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 2, v___x_468_);
lean_ctor_set(v___x_463_, 1, v_v_433_);
lean_ctor_set(v___x_463_, 0, v_a_465_);
v___x_470_ = v___x_463_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_v_433_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
lean_dec(v_a_465_);
lean_del_object(v___x_463_);
lean_dec(v_v_433_);
v_fuel_392_ = v_n_399_;
v_p_u2081_393_ = v_p_434_;
v_p_u2082_394_ = v_p_437_;
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
lean_object* v___x_477_; 
v___x_477_ = lean_unsigned_to_nat(100000000u);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_combine(lean_object* v_p_u2081_478_, lean_object* v_p_u2082_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(100000000u);
v___x_481_ = l_Int_Linear_Poly_combine_x27(v___x_480_, v_p_u2081_478_, v_p_u2082_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go(lean_object* v_coeff_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
switch(lean_obj_tag(v_a_483_))
{
case 0:
{
lean_object* v_v_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_v_485_ = lean_ctor_get(v_a_483_, 0);
v___x_486_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_487_ = lean_int_dec_eq(v_v_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_int_mul(v_coeff_482_, v_v_485_);
lean_dec(v_coeff_482_);
v___x_489_ = l_Int_Linear_Poly_addConst(v_a_484_, v___x_488_);
lean_dec(v___x_488_);
return v___x_489_;
}
else
{
lean_dec(v_coeff_482_);
return v_a_484_;
}
}
case 1:
{
lean_object* v_i_490_; lean_object* v___x_491_; 
v_i_490_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_i_490_);
v___x_491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_491_, 0, v_coeff_482_);
lean_ctor_set(v___x_491_, 1, v_i_490_);
lean_ctor_set(v___x_491_, 2, v_a_484_);
return v___x_491_;
}
case 2:
{
lean_object* v_a_492_; lean_object* v_b_493_; lean_object* v___x_494_; 
v_a_492_ = lean_ctor_get(v_a_483_, 0);
v_b_493_ = lean_ctor_get(v_a_483_, 1);
lean_inc(v_coeff_482_);
v___x_494_ = l_Int_Linear_Expr_toPoly_x27_go(v_coeff_482_, v_b_493_, v_a_484_);
v_a_483_ = v_a_492_;
v_a_484_ = v___x_494_;
goto _start;
}
case 3:
{
lean_object* v_a_496_; lean_object* v_b_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_a_496_ = lean_ctor_get(v_a_483_, 0);
v_b_497_ = lean_ctor_get(v_a_483_, 1);
v___x_498_ = lean_int_neg(v_coeff_482_);
v___x_499_ = l_Int_Linear_Expr_toPoly_x27_go(v___x_498_, v_b_497_, v_a_484_);
v_a_483_ = v_a_496_;
v_a_484_ = v___x_499_;
goto _start;
}
case 4:
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v_a_483_, 0);
v___x_502_ = lean_int_neg(v_coeff_482_);
lean_dec(v_coeff_482_);
v_coeff_482_ = v___x_502_;
v_a_483_ = v_a_501_;
goto _start;
}
case 5:
{
lean_object* v_k_504_; lean_object* v_a_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_k_504_ = lean_ctor_get(v_a_483_, 0);
v_a_505_ = lean_ctor_get(v_a_483_, 1);
v___x_506_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_507_ = lean_int_dec_eq(v_k_504_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_int_mul(v_coeff_482_, v_k_504_);
lean_dec(v_coeff_482_);
v_coeff_482_ = v___x_508_;
v_a_483_ = v_a_505_;
goto _start;
}
else
{
lean_dec(v_coeff_482_);
return v_a_484_;
}
}
default: 
{
lean_object* v_a_510_; lean_object* v_k_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_a_510_ = lean_ctor_get(v_a_483_, 0);
v_k_511_ = lean_ctor_get(v_a_483_, 1);
v___x_512_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_513_ = lean_int_dec_eq(v_k_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_int_mul(v_coeff_482_, v_k_511_);
lean_dec(v_coeff_482_);
v_coeff_482_ = v___x_514_;
v_a_483_ = v_a_510_;
goto _start;
}
else
{
lean_dec(v_coeff_482_);
return v_a_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27_go___boxed(lean_object* v_coeff_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Int_Linear_Expr_toPoly_x27_go(v_coeff_516_, v_a_517_, v_a_518_);
lean_dec_ref(v_a_517_);
return v_res_519_;
}
}
static lean_object* _init_l_Int_Linear_Expr_toPoly_x27___closed__0(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_to_int(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Int_Linear_Expr_toPoly_x27___closed__1(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27(lean_object* v_e_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
v___x_526_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__1, &l_Int_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__1);
v___x_527_ = l_Int_Linear_Expr_toPoly_x27_go(v___x_525_, v_e_524_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_toPoly_x27___boxed(lean_object* v_e_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Int_Linear_Expr_toPoly_x27(v_e_528_);
lean_dec_ref(v_e_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm(lean_object* v_e_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Int_Linear_Expr_toPoly_x27(v_e_530_);
v___x_532_ = l_Int_Linear_Poly_norm(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_norm___boxed(lean_object* v_e_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Int_Linear_Expr_norm(v_e_533_);
lean_dec_ref(v_e_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cdiv(lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_int_neg(v_a_535_);
v___x_538_ = lean_int_ediv(v___x_537_, v_b_536_);
lean_dec(v___x_537_);
v___x_539_ = lean_int_neg(v___x_538_);
lean_dec(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cdiv___boxed(lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Int_Linear_cdiv(v_a_540_, v_b_541_);
lean_dec(v_b_541_);
lean_dec(v_a_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cmod(lean_object* v_a_543_, lean_object* v_b_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_int_neg(v_a_543_);
v___x_546_ = lean_int_emod(v___x_545_, v_b_544_);
lean_dec(v___x_545_);
v___x_547_ = lean_int_neg(v___x_546_);
lean_dec(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_cmod___boxed(lean_object* v_a_548_, lean_object* v_b_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Int_Linear_cmod(v_a_548_, v_b_549_);
lean_dec(v_b_549_);
lean_dec(v_a_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst(lean_object* v_x_551_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_k_552_; 
v_k_552_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_k_552_);
return v_k_552_;
}
else
{
lean_object* v_p_553_; 
v_p_553_ = lean_ctor_get(v_x_551_, 2);
v_x_551_ = v_p_553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_getConst___boxed(lean_object* v_x_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Int_Linear_Poly_getConst(v_x_555_);
lean_dec_ref(v_x_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div(lean_object* v_k_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v_k_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_k_559_ = lean_ctor_get(v_x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_k_559_);
lean_dec(v_x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = l_Int_Linear_cdiv(v_k_559_, v_k_557_);
lean_dec(v_k_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_k_568_; lean_object* v_v_569_; lean_object* v_p_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_579_; 
v_k_568_ = lean_ctor_get(v_x_558_, 0);
v_v_569_ = lean_ctor_get(v_x_558_, 1);
v_p_570_ = lean_ctor_get(v_x_558_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_579_ == 0)
{
v___x_572_ = v_x_558_;
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_p_570_);
lean_inc(v_v_569_);
lean_inc(v_k_568_);
lean_dec(v_x_558_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = lean_int_ediv(v_k_568_, v_k_557_);
lean_dec(v_k_568_);
v___x_575_ = l_Int_Linear_Poly_div(v_k_557_, v_p_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 2, v___x_575_);
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_v_569_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_div___boxed(lean_object* v_k_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Int_Linear_Poly_div(v_k_580_, v_x_581_);
lean_dec(v_k_580_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divAll(lean_object* v_k_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_k_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_k_585_ = lean_ctor_get(v_x_584_, 0);
v___x_586_ = lean_int_emod(v_k_585_, v_k_583_);
v___x_587_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_588_ = lean_int_dec_eq(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
return v___x_588_;
}
else
{
lean_object* v_k_589_; lean_object* v_p_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_k_589_ = lean_ctor_get(v_x_584_, 0);
v_p_590_ = lean_ctor_get(v_x_584_, 2);
v___x_591_ = lean_int_emod(v_k_589_, v_k_583_);
v___x_592_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_593_ = lean_int_dec_eq(v___x_591_, v___x_592_);
lean_dec(v___x_591_);
if (v___x_593_ == 0)
{
return v___x_593_;
}
else
{
v_x_584_ = v_p_590_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divAll___boxed(lean_object* v_k_595_, lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Int_Linear_Poly_divAll(v_k_595_, v_x_596_);
lean_dec_ref(v_x_596_);
lean_dec(v_k_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_divCoeffs(lean_object* v_k_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
uint8_t v___x_601_; 
v___x_601_ = 1;
return v___x_601_;
}
else
{
lean_object* v_k_602_; lean_object* v_p_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_k_602_ = lean_ctor_get(v_x_600_, 0);
v_p_603_ = lean_ctor_get(v_x_600_, 2);
v___x_604_ = lean_int_emod(v_k_602_, v_k_599_);
v___x_605_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_606_ = lean_int_dec_eq(v___x_604_, v___x_605_);
lean_dec(v___x_604_);
if (v___x_606_ == 0)
{
return v___x_606_;
}
else
{
v_x_600_ = v_p_603_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_divCoeffs___boxed(lean_object* v_k_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Int_Linear_Poly_divCoeffs(v_k_608_, v_x_609_);
lean_dec_ref(v_x_609_);
lean_dec(v_k_608_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27(lean_object* v_p_612_, lean_object* v_k_613_){
_start:
{
if (lean_obj_tag(v_p_612_) == 0)
{
lean_object* v_k_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v_k_614_ = lean_ctor_get(v_p_612_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_p_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_616_ = v_p_612_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_k_614_);
lean_dec(v_p_612_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_int_mul(v_k_613_, v_k_614_);
lean_dec(v_k_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_k_623_; lean_object* v_v_624_; lean_object* v_p_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_634_; 
v_k_623_ = lean_ctor_get(v_p_612_, 0);
v_v_624_ = lean_ctor_get(v_p_612_, 1);
v_p_625_ = lean_ctor_get(v_p_612_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_p_612_);
if (v_isSharedCheck_634_ == 0)
{
v___x_627_ = v_p_612_;
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_p_625_);
lean_inc(v_v_624_);
lean_inc(v_k_623_);
lean_dec(v_p_612_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_629_ = lean_int_mul(v_k_613_, v_k_623_);
lean_dec(v_k_623_);
v___x_630_ = l_Int_Linear_Poly_mul_x27(v_p_625_, v_k_613_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 2, v___x_630_);
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_632_ = v___x_627_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_v_624_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul_x27___boxed(lean_object* v_p_635_, lean_object* v_k_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Int_Linear_Poly_mul_x27(v_p_635_, v_k_636_);
lean_dec(v_k_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul(lean_object* v_p_638_, lean_object* v_k_639_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_641_ = lean_int_dec_eq(v_k_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = l_Int_Linear_Poly_mul_x27(v_p_638_, v_k_639_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
lean_dec_ref(v_p_638_);
v___x_643_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__1, &l_Int_Linear_Expr_toPoly_x27___closed__1_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__1);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_mul___boxed(lean_object* v_p_644_, lean_object* v_k_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Int_Linear_Poly_mul(v_p_644_, v_k_645_);
lean_dec(v_k_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(lean_object* v_fuel_647_, lean_object* v_h__1_648_, lean_object* v_h__2_649_){
_start:
{
lean_object* v_zero_650_; uint8_t v_isZero_651_; 
v_zero_650_ = lean_unsigned_to_nat(0u);
v_isZero_651_ = lean_nat_dec_eq(v_fuel_647_, v_zero_650_);
if (v_isZero_651_ == 1)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_h__2_649_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_apply_1(v_h__1_648_, v___x_652_);
return v___x_653_;
}
else
{
lean_object* v_one_654_; lean_object* v_n_655_; lean_object* v___x_656_; 
lean_dec(v_h__1_648_);
v_one_654_ = lean_unsigned_to_nat(1u);
v_n_655_ = lean_nat_sub(v_fuel_647_, v_one_654_);
v___x_656_ = lean_apply_1(v_h__2_649_, v_n_655_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg___boxed(lean_object* v_fuel_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___redArg(v_fuel_657_, v_h__1_658_, v_h__2_659_);
lean_dec(v_fuel_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(lean_object* v_motive_661_, lean_object* v_fuel_662_, lean_object* v_h__1_663_, lean_object* v_h__2_664_){
_start:
{
lean_object* v_zero_665_; uint8_t v_isZero_666_; 
v_zero_665_ = lean_unsigned_to_nat(0u);
v_isZero_666_ = lean_nat_dec_eq(v_fuel_662_, v_zero_665_);
if (v_isZero_666_ == 1)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_h__2_664_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_apply_1(v_h__1_663_, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v_one_669_; lean_object* v_n_670_; lean_object* v___x_671_; 
lean_dec(v_h__1_663_);
v_one_669_ = lean_unsigned_to_nat(1u);
v_n_670_ = lean_nat_sub(v_fuel_662_, v_one_669_);
v___x_671_ = lean_apply_1(v_h__2_664_, v_n_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter___boxed(lean_object* v_motive_672_, lean_object* v_fuel_673_, lean_object* v_h__1_674_, lean_object* v_h__2_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__3_splitter(v_motive_672_, v_fuel_673_, v_h__1_674_, v_h__2_675_);
lean_dec(v_fuel_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter___redArg(lean_object* v_p_u2081_677_, lean_object* v_p_u2082_678_, lean_object* v_h__1_679_, lean_object* v_h__2_680_, lean_object* v_h__3_681_, lean_object* v_h__4_682_){
_start:
{
if (lean_obj_tag(v_p_u2081_677_) == 0)
{
lean_dec(v_h__4_682_);
lean_dec(v_h__3_681_);
if (lean_obj_tag(v_p_u2082_678_) == 0)
{
lean_object* v_k_683_; lean_object* v_k_684_; lean_object* v___x_685_; 
lean_dec(v_h__2_680_);
v_k_683_ = lean_ctor_get(v_p_u2081_677_, 0);
lean_inc(v_k_683_);
lean_dec_ref(v_p_u2081_677_);
v_k_684_ = lean_ctor_get(v_p_u2082_678_, 0);
lean_inc(v_k_684_);
lean_dec_ref(v_p_u2082_678_);
v___x_685_ = lean_apply_2(v_h__1_679_, v_k_683_, v_k_684_);
return v___x_685_;
}
else
{
lean_object* v_k_686_; lean_object* v_k_687_; lean_object* v_v_688_; lean_object* v_p_689_; lean_object* v___x_690_; 
lean_dec(v_h__1_679_);
v_k_686_ = lean_ctor_get(v_p_u2081_677_, 0);
lean_inc(v_k_686_);
lean_dec_ref(v_p_u2081_677_);
v_k_687_ = lean_ctor_get(v_p_u2082_678_, 0);
lean_inc(v_k_687_);
v_v_688_ = lean_ctor_get(v_p_u2082_678_, 1);
lean_inc(v_v_688_);
v_p_689_ = lean_ctor_get(v_p_u2082_678_, 2);
lean_inc_ref(v_p_689_);
lean_dec_ref(v_p_u2082_678_);
v___x_690_ = lean_apply_4(v_h__2_680_, v_k_686_, v_k_687_, v_v_688_, v_p_689_);
return v___x_690_;
}
}
else
{
lean_dec(v_h__2_680_);
lean_dec(v_h__1_679_);
if (lean_obj_tag(v_p_u2082_678_) == 0)
{
lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_p_693_; lean_object* v_k_694_; lean_object* v___x_695_; 
lean_dec(v_h__4_682_);
v_k_691_ = lean_ctor_get(v_p_u2081_677_, 0);
lean_inc(v_k_691_);
v_v_692_ = lean_ctor_get(v_p_u2081_677_, 1);
lean_inc(v_v_692_);
v_p_693_ = lean_ctor_get(v_p_u2081_677_, 2);
lean_inc_ref(v_p_693_);
lean_dec_ref(v_p_u2081_677_);
v_k_694_ = lean_ctor_get(v_p_u2082_678_, 0);
lean_inc(v_k_694_);
lean_dec_ref(v_p_u2082_678_);
v___x_695_ = lean_apply_4(v_h__3_681_, v_k_691_, v_v_692_, v_p_693_, v_k_694_);
return v___x_695_;
}
else
{
lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_p_698_; lean_object* v_k_699_; lean_object* v_v_700_; lean_object* v_p_701_; lean_object* v___x_702_; 
lean_dec(v_h__3_681_);
v_k_696_ = lean_ctor_get(v_p_u2081_677_, 0);
lean_inc(v_k_696_);
v_v_697_ = lean_ctor_get(v_p_u2081_677_, 1);
lean_inc(v_v_697_);
v_p_698_ = lean_ctor_get(v_p_u2081_677_, 2);
lean_inc_ref(v_p_698_);
lean_dec_ref(v_p_u2081_677_);
v_k_699_ = lean_ctor_get(v_p_u2082_678_, 0);
lean_inc(v_k_699_);
v_v_700_ = lean_ctor_get(v_p_u2082_678_, 1);
lean_inc(v_v_700_);
v_p_701_ = lean_ctor_get(v_p_u2082_678_, 2);
lean_inc_ref(v_p_701_);
lean_dec_ref(v_p_u2082_678_);
v___x_702_ = lean_apply_6(v_h__4_682_, v_k_696_, v_v_697_, v_p_698_, v_k_699_, v_v_700_, v_p_701_);
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_combine_x27_match__1_splitter(lean_object* v_motive_703_, lean_object* v_p_u2081_704_, lean_object* v_p_u2082_705_, lean_object* v_h__1_706_, lean_object* v_h__2_707_, lean_object* v_h__3_708_, lean_object* v_h__4_709_){
_start:
{
if (lean_obj_tag(v_p_u2081_704_) == 0)
{
lean_dec(v_h__4_709_);
lean_dec(v_h__3_708_);
if (lean_obj_tag(v_p_u2082_705_) == 0)
{
lean_object* v_k_710_; lean_object* v_k_711_; lean_object* v___x_712_; 
lean_dec(v_h__2_707_);
v_k_710_ = lean_ctor_get(v_p_u2081_704_, 0);
lean_inc(v_k_710_);
lean_dec_ref(v_p_u2081_704_);
v_k_711_ = lean_ctor_get(v_p_u2082_705_, 0);
lean_inc(v_k_711_);
lean_dec_ref(v_p_u2082_705_);
v___x_712_ = lean_apply_2(v_h__1_706_, v_k_710_, v_k_711_);
return v___x_712_;
}
else
{
lean_object* v_k_713_; lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v_p_716_; lean_object* v___x_717_; 
lean_dec(v_h__1_706_);
v_k_713_ = lean_ctor_get(v_p_u2081_704_, 0);
lean_inc(v_k_713_);
lean_dec_ref(v_p_u2081_704_);
v_k_714_ = lean_ctor_get(v_p_u2082_705_, 0);
lean_inc(v_k_714_);
v_v_715_ = lean_ctor_get(v_p_u2082_705_, 1);
lean_inc(v_v_715_);
v_p_716_ = lean_ctor_get(v_p_u2082_705_, 2);
lean_inc_ref(v_p_716_);
lean_dec_ref(v_p_u2082_705_);
v___x_717_ = lean_apply_4(v_h__2_707_, v_k_713_, v_k_714_, v_v_715_, v_p_716_);
return v___x_717_;
}
}
else
{
lean_dec(v_h__2_707_);
lean_dec(v_h__1_706_);
if (lean_obj_tag(v_p_u2082_705_) == 0)
{
lean_object* v_k_718_; lean_object* v_v_719_; lean_object* v_p_720_; lean_object* v_k_721_; lean_object* v___x_722_; 
lean_dec(v_h__4_709_);
v_k_718_ = lean_ctor_get(v_p_u2081_704_, 0);
lean_inc(v_k_718_);
v_v_719_ = lean_ctor_get(v_p_u2081_704_, 1);
lean_inc(v_v_719_);
v_p_720_ = lean_ctor_get(v_p_u2081_704_, 2);
lean_inc_ref(v_p_720_);
lean_dec_ref(v_p_u2081_704_);
v_k_721_ = lean_ctor_get(v_p_u2082_705_, 0);
lean_inc(v_k_721_);
lean_dec_ref(v_p_u2082_705_);
v___x_722_ = lean_apply_4(v_h__3_708_, v_k_718_, v_v_719_, v_p_720_, v_k_721_);
return v___x_722_;
}
else
{
lean_object* v_k_723_; lean_object* v_v_724_; lean_object* v_p_725_; lean_object* v_k_726_; lean_object* v_v_727_; lean_object* v_p_728_; lean_object* v___x_729_; 
lean_dec(v_h__3_708_);
v_k_723_ = lean_ctor_get(v_p_u2081_704_, 0);
lean_inc(v_k_723_);
v_v_724_ = lean_ctor_get(v_p_u2081_704_, 1);
lean_inc(v_v_724_);
v_p_725_ = lean_ctor_get(v_p_u2081_704_, 2);
lean_inc_ref(v_p_725_);
lean_dec_ref(v_p_u2081_704_);
v_k_726_ = lean_ctor_get(v_p_u2082_705_, 0);
lean_inc(v_k_726_);
v_v_727_ = lean_ctor_get(v_p_u2082_705_, 1);
lean_inc(v_v_727_);
v_p_728_ = lean_ctor_get(v_p_u2082_705_, 2);
lean_inc_ref(v_p_728_);
lean_dec_ref(v_p_u2082_705_);
v___x_729_ = lean_apply_6(v_h__4_709_, v_k_723_, v_v_724_, v_p_725_, v_k_726_, v_v_727_, v_p_728_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter___redArg(lean_object* v_x_730_, lean_object* v_h__1_731_, lean_object* v_h__2_732_, lean_object* v_h__3_733_, lean_object* v_h__4_734_, lean_object* v_h__5_735_, lean_object* v_h__6_736_, lean_object* v_h__7_737_){
_start:
{
switch(lean_obj_tag(v_x_730_))
{
case 0:
{
lean_object* v_v_738_; lean_object* v___x_739_; 
lean_dec(v_h__7_737_);
lean_dec(v_h__6_736_);
lean_dec(v_h__5_735_);
lean_dec(v_h__3_733_);
lean_dec(v_h__2_732_);
lean_dec(v_h__1_731_);
v_v_738_ = lean_ctor_get(v_x_730_, 0);
lean_inc(v_v_738_);
lean_dec_ref(v_x_730_);
v___x_739_ = lean_apply_1(v_h__4_734_, v_v_738_);
return v___x_739_;
}
case 1:
{
lean_object* v_i_740_; lean_object* v___x_741_; 
lean_dec(v_h__7_737_);
lean_dec(v_h__6_736_);
lean_dec(v_h__4_734_);
lean_dec(v_h__3_733_);
lean_dec(v_h__2_732_);
lean_dec(v_h__1_731_);
v_i_740_ = lean_ctor_get(v_x_730_, 0);
lean_inc(v_i_740_);
lean_dec_ref(v_x_730_);
v___x_741_ = lean_apply_1(v_h__5_735_, v_i_740_);
return v___x_741_;
}
case 2:
{
lean_object* v_a_742_; lean_object* v_b_743_; lean_object* v___x_744_; 
lean_dec(v_h__7_737_);
lean_dec(v_h__6_736_);
lean_dec(v_h__5_735_);
lean_dec(v_h__4_734_);
lean_dec(v_h__3_733_);
lean_dec(v_h__2_732_);
v_a_742_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_a_742_);
v_b_743_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_b_743_);
lean_dec_ref(v_x_730_);
v___x_744_ = lean_apply_2(v_h__1_731_, v_a_742_, v_b_743_);
return v___x_744_;
}
case 3:
{
lean_object* v_a_745_; lean_object* v_b_746_; lean_object* v___x_747_; 
lean_dec(v_h__7_737_);
lean_dec(v_h__6_736_);
lean_dec(v_h__5_735_);
lean_dec(v_h__4_734_);
lean_dec(v_h__3_733_);
lean_dec(v_h__1_731_);
v_a_745_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_a_745_);
v_b_746_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_b_746_);
lean_dec_ref(v_x_730_);
v___x_747_ = lean_apply_2(v_h__2_732_, v_a_745_, v_b_746_);
return v___x_747_;
}
case 4:
{
lean_object* v_a_748_; lean_object* v___x_749_; 
lean_dec(v_h__7_737_);
lean_dec(v_h__6_736_);
lean_dec(v_h__5_735_);
lean_dec(v_h__4_734_);
lean_dec(v_h__2_732_);
lean_dec(v_h__1_731_);
v_a_748_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_a_748_);
lean_dec_ref(v_x_730_);
v___x_749_ = lean_apply_1(v_h__3_733_, v_a_748_);
return v___x_749_;
}
case 5:
{
lean_object* v_k_750_; lean_object* v_a_751_; lean_object* v___x_752_; 
lean_dec(v_h__7_737_);
lean_dec(v_h__5_735_);
lean_dec(v_h__4_734_);
lean_dec(v_h__3_733_);
lean_dec(v_h__2_732_);
lean_dec(v_h__1_731_);
v_k_750_ = lean_ctor_get(v_x_730_, 0);
lean_inc(v_k_750_);
v_a_751_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_a_751_);
lean_dec_ref(v_x_730_);
v___x_752_ = lean_apply_2(v_h__6_736_, v_k_750_, v_a_751_);
return v___x_752_;
}
default: 
{
lean_object* v_a_753_; lean_object* v_k_754_; lean_object* v___x_755_; 
lean_dec(v_h__6_736_);
lean_dec(v_h__5_735_);
lean_dec(v_h__4_734_);
lean_dec(v_h__3_733_);
lean_dec(v_h__2_732_);
lean_dec(v_h__1_731_);
v_a_753_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_a_753_);
v_k_754_ = lean_ctor_get(v_x_730_, 1);
lean_inc(v_k_754_);
lean_dec_ref(v_x_730_);
v___x_755_ = lean_apply_2(v_h__7_737_, v_a_753_, v_k_754_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_denote_match__1_splitter(lean_object* v_motive_756_, lean_object* v_x_757_, lean_object* v_h__1_758_, lean_object* v_h__2_759_, lean_object* v_h__3_760_, lean_object* v_h__4_761_, lean_object* v_h__5_762_, lean_object* v_h__6_763_, lean_object* v_h__7_764_){
_start:
{
switch(lean_obj_tag(v_x_757_))
{
case 0:
{
lean_object* v_v_765_; lean_object* v___x_766_; 
lean_dec(v_h__7_764_);
lean_dec(v_h__6_763_);
lean_dec(v_h__5_762_);
lean_dec(v_h__3_760_);
lean_dec(v_h__2_759_);
lean_dec(v_h__1_758_);
v_v_765_ = lean_ctor_get(v_x_757_, 0);
lean_inc(v_v_765_);
lean_dec_ref(v_x_757_);
v___x_766_ = lean_apply_1(v_h__4_761_, v_v_765_);
return v___x_766_;
}
case 1:
{
lean_object* v_i_767_; lean_object* v___x_768_; 
lean_dec(v_h__7_764_);
lean_dec(v_h__6_763_);
lean_dec(v_h__4_761_);
lean_dec(v_h__3_760_);
lean_dec(v_h__2_759_);
lean_dec(v_h__1_758_);
v_i_767_ = lean_ctor_get(v_x_757_, 0);
lean_inc(v_i_767_);
lean_dec_ref(v_x_757_);
v___x_768_ = lean_apply_1(v_h__5_762_, v_i_767_);
return v___x_768_;
}
case 2:
{
lean_object* v_a_769_; lean_object* v_b_770_; lean_object* v___x_771_; 
lean_dec(v_h__7_764_);
lean_dec(v_h__6_763_);
lean_dec(v_h__5_762_);
lean_dec(v_h__4_761_);
lean_dec(v_h__3_760_);
lean_dec(v_h__2_759_);
v_a_769_ = lean_ctor_get(v_x_757_, 0);
lean_inc_ref(v_a_769_);
v_b_770_ = lean_ctor_get(v_x_757_, 1);
lean_inc_ref(v_b_770_);
lean_dec_ref(v_x_757_);
v___x_771_ = lean_apply_2(v_h__1_758_, v_a_769_, v_b_770_);
return v___x_771_;
}
case 3:
{
lean_object* v_a_772_; lean_object* v_b_773_; lean_object* v___x_774_; 
lean_dec(v_h__7_764_);
lean_dec(v_h__6_763_);
lean_dec(v_h__5_762_);
lean_dec(v_h__4_761_);
lean_dec(v_h__3_760_);
lean_dec(v_h__1_758_);
v_a_772_ = lean_ctor_get(v_x_757_, 0);
lean_inc_ref(v_a_772_);
v_b_773_ = lean_ctor_get(v_x_757_, 1);
lean_inc_ref(v_b_773_);
lean_dec_ref(v_x_757_);
v___x_774_ = lean_apply_2(v_h__2_759_, v_a_772_, v_b_773_);
return v___x_774_;
}
case 4:
{
lean_object* v_a_775_; lean_object* v___x_776_; 
lean_dec(v_h__7_764_);
lean_dec(v_h__6_763_);
lean_dec(v_h__5_762_);
lean_dec(v_h__4_761_);
lean_dec(v_h__2_759_);
lean_dec(v_h__1_758_);
v_a_775_ = lean_ctor_get(v_x_757_, 0);
lean_inc_ref(v_a_775_);
lean_dec_ref(v_x_757_);
v___x_776_ = lean_apply_1(v_h__3_760_, v_a_775_);
return v___x_776_;
}
case 5:
{
lean_object* v_k_777_; lean_object* v_a_778_; lean_object* v___x_779_; 
lean_dec(v_h__7_764_);
lean_dec(v_h__5_762_);
lean_dec(v_h__4_761_);
lean_dec(v_h__3_760_);
lean_dec(v_h__2_759_);
lean_dec(v_h__1_758_);
v_k_777_ = lean_ctor_get(v_x_757_, 0);
lean_inc(v_k_777_);
v_a_778_ = lean_ctor_get(v_x_757_, 1);
lean_inc_ref(v_a_778_);
lean_dec_ref(v_x_757_);
v___x_779_ = lean_apply_2(v_h__6_763_, v_k_777_, v_a_778_);
return v___x_779_;
}
default: 
{
lean_object* v_a_780_; lean_object* v_k_781_; lean_object* v___x_782_; 
lean_dec(v_h__6_763_);
lean_dec(v_h__5_762_);
lean_dec(v_h__4_761_);
lean_dec(v_h__3_760_);
lean_dec(v_h__2_759_);
lean_dec(v_h__1_758_);
v_a_780_ = lean_ctor_get(v_x_757_, 0);
lean_inc_ref(v_a_780_);
v_k_781_ = lean_ctor_get(v_x_757_, 1);
lean_inc(v_k_781_);
lean_dec_ref(v_x_757_);
v___x_782_ = lean_apply_2(v_h__7_764_, v_a_780_, v_k_781_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter___redArg(lean_object* v_x_783_, lean_object* v_h__1_784_, lean_object* v_h__2_785_, lean_object* v_h__3_786_, lean_object* v_h__4_787_, lean_object* v_h__5_788_, lean_object* v_h__6_789_, lean_object* v_h__7_790_){
_start:
{
switch(lean_obj_tag(v_x_783_))
{
case 0:
{
lean_object* v_v_791_; lean_object* v___x_792_; 
lean_dec(v_h__7_790_);
lean_dec(v_h__6_789_);
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
v_v_791_ = lean_ctor_get(v_x_783_, 0);
lean_inc(v_v_791_);
lean_dec_ref(v_x_783_);
v___x_792_ = lean_apply_1(v_h__1_784_, v_v_791_);
return v___x_792_;
}
case 1:
{
lean_object* v_i_793_; lean_object* v___x_794_; 
lean_dec(v_h__7_790_);
lean_dec(v_h__6_789_);
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__1_784_);
v_i_793_ = lean_ctor_get(v_x_783_, 0);
lean_inc(v_i_793_);
lean_dec_ref(v_x_783_);
v___x_794_ = lean_apply_1(v_h__2_785_, v_i_793_);
return v___x_794_;
}
case 2:
{
lean_object* v_a_795_; lean_object* v_b_796_; lean_object* v___x_797_; 
lean_dec(v_h__7_790_);
lean_dec(v_h__6_789_);
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_795_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_a_795_);
v_b_796_ = lean_ctor_get(v_x_783_, 1);
lean_inc_ref(v_b_796_);
lean_dec_ref(v_x_783_);
v___x_797_ = lean_apply_2(v_h__3_786_, v_a_795_, v_b_796_);
return v___x_797_;
}
case 3:
{
lean_object* v_a_798_; lean_object* v_b_799_; lean_object* v___x_800_; 
lean_dec(v_h__7_790_);
lean_dec(v_h__6_789_);
lean_dec(v_h__5_788_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_798_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_a_798_);
v_b_799_ = lean_ctor_get(v_x_783_, 1);
lean_inc_ref(v_b_799_);
lean_dec_ref(v_x_783_);
v___x_800_ = lean_apply_2(v_h__4_787_, v_a_798_, v_b_799_);
return v___x_800_;
}
case 4:
{
lean_object* v_a_801_; lean_object* v___x_802_; 
lean_dec(v_h__6_789_);
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_801_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_a_801_);
lean_dec_ref(v_x_783_);
v___x_802_ = lean_apply_1(v_h__7_790_, v_a_801_);
return v___x_802_;
}
case 5:
{
lean_object* v_k_803_; lean_object* v_a_804_; lean_object* v___x_805_; 
lean_dec(v_h__7_790_);
lean_dec(v_h__6_789_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_k_803_ = lean_ctor_get(v_x_783_, 0);
lean_inc(v_k_803_);
v_a_804_ = lean_ctor_get(v_x_783_, 1);
lean_inc_ref(v_a_804_);
lean_dec_ref(v_x_783_);
v___x_805_ = lean_apply_2(v_h__5_788_, v_k_803_, v_a_804_);
return v___x_805_;
}
default: 
{
lean_object* v_a_806_; lean_object* v_k_807_; lean_object* v___x_808_; 
lean_dec(v_h__7_790_);
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_806_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_a_806_);
v_k_807_ = lean_ctor_get(v_x_783_, 1);
lean_inc(v_k_807_);
lean_dec_ref(v_x_783_);
v___x_808_ = lean_apply_2(v_h__6_789_, v_a_806_, v_k_807_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Expr_toPoly_x27_go_match__1_splitter(lean_object* v_motive_809_, lean_object* v_x_810_, lean_object* v_h__1_811_, lean_object* v_h__2_812_, lean_object* v_h__3_813_, lean_object* v_h__4_814_, lean_object* v_h__5_815_, lean_object* v_h__6_816_, lean_object* v_h__7_817_){
_start:
{
switch(lean_obj_tag(v_x_810_))
{
case 0:
{
lean_object* v_v_818_; lean_object* v___x_819_; 
lean_dec(v_h__7_817_);
lean_dec(v_h__6_816_);
lean_dec(v_h__5_815_);
lean_dec(v_h__4_814_);
lean_dec(v_h__3_813_);
lean_dec(v_h__2_812_);
v_v_818_ = lean_ctor_get(v_x_810_, 0);
lean_inc(v_v_818_);
lean_dec_ref(v_x_810_);
v___x_819_ = lean_apply_1(v_h__1_811_, v_v_818_);
return v___x_819_;
}
case 1:
{
lean_object* v_i_820_; lean_object* v___x_821_; 
lean_dec(v_h__7_817_);
lean_dec(v_h__6_816_);
lean_dec(v_h__5_815_);
lean_dec(v_h__4_814_);
lean_dec(v_h__3_813_);
lean_dec(v_h__1_811_);
v_i_820_ = lean_ctor_get(v_x_810_, 0);
lean_inc(v_i_820_);
lean_dec_ref(v_x_810_);
v___x_821_ = lean_apply_1(v_h__2_812_, v_i_820_);
return v___x_821_;
}
case 2:
{
lean_object* v_a_822_; lean_object* v_b_823_; lean_object* v___x_824_; 
lean_dec(v_h__7_817_);
lean_dec(v_h__6_816_);
lean_dec(v_h__5_815_);
lean_dec(v_h__4_814_);
lean_dec(v_h__2_812_);
lean_dec(v_h__1_811_);
v_a_822_ = lean_ctor_get(v_x_810_, 0);
lean_inc_ref(v_a_822_);
v_b_823_ = lean_ctor_get(v_x_810_, 1);
lean_inc_ref(v_b_823_);
lean_dec_ref(v_x_810_);
v___x_824_ = lean_apply_2(v_h__3_813_, v_a_822_, v_b_823_);
return v___x_824_;
}
case 3:
{
lean_object* v_a_825_; lean_object* v_b_826_; lean_object* v___x_827_; 
lean_dec(v_h__7_817_);
lean_dec(v_h__6_816_);
lean_dec(v_h__5_815_);
lean_dec(v_h__3_813_);
lean_dec(v_h__2_812_);
lean_dec(v_h__1_811_);
v_a_825_ = lean_ctor_get(v_x_810_, 0);
lean_inc_ref(v_a_825_);
v_b_826_ = lean_ctor_get(v_x_810_, 1);
lean_inc_ref(v_b_826_);
lean_dec_ref(v_x_810_);
v___x_827_ = lean_apply_2(v_h__4_814_, v_a_825_, v_b_826_);
return v___x_827_;
}
case 4:
{
lean_object* v_a_828_; lean_object* v___x_829_; 
lean_dec(v_h__6_816_);
lean_dec(v_h__5_815_);
lean_dec(v_h__4_814_);
lean_dec(v_h__3_813_);
lean_dec(v_h__2_812_);
lean_dec(v_h__1_811_);
v_a_828_ = lean_ctor_get(v_x_810_, 0);
lean_inc_ref(v_a_828_);
lean_dec_ref(v_x_810_);
v___x_829_ = lean_apply_1(v_h__7_817_, v_a_828_);
return v___x_829_;
}
case 5:
{
lean_object* v_k_830_; lean_object* v_a_831_; lean_object* v___x_832_; 
lean_dec(v_h__7_817_);
lean_dec(v_h__6_816_);
lean_dec(v_h__4_814_);
lean_dec(v_h__3_813_);
lean_dec(v_h__2_812_);
lean_dec(v_h__1_811_);
v_k_830_ = lean_ctor_get(v_x_810_, 0);
lean_inc(v_k_830_);
v_a_831_ = lean_ctor_get(v_x_810_, 1);
lean_inc_ref(v_a_831_);
lean_dec_ref(v_x_810_);
v___x_832_ = lean_apply_2(v_h__5_815_, v_k_830_, v_a_831_);
return v___x_832_;
}
default: 
{
lean_object* v_a_833_; lean_object* v_k_834_; lean_object* v___x_835_; 
lean_dec(v_h__7_817_);
lean_dec(v_h__5_815_);
lean_dec(v_h__4_814_);
lean_dec(v_h__3_813_);
lean_dec(v_h__2_812_);
lean_dec(v_h__1_811_);
v_a_833_ = lean_ctor_get(v_x_810_, 0);
lean_inc_ref(v_a_833_);
v_k_834_ = lean_ctor_get(v_x_810_, 1);
lean_inc(v_k_834_);
lean_dec_ref(v_x_810_);
v___x_835_ = lean_apply_2(v_h__6_816_, v_a_833_, v_k_834_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object* v_p_836_){
_start:
{
if (lean_obj_tag(v_p_836_) == 0)
{
lean_object* v_k_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_k_837_ = lean_ctor_get(v_p_836_, 0);
v___x_838_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_839_ = lean_int_dec_eq(v_k_837_, v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = 1;
return v___x_840_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = 0;
return v___x_841_;
}
}
else
{
uint8_t v___x_842_; 
v___x_842_ = 0;
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatEq___boxed(lean_object* v_p_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Int_Linear_Poly_isUnsatEq(v_p_843_);
lean_dec_ref(v_p_843_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidEq(lean_object* v_p_846_){
_start:
{
if (lean_obj_tag(v_p_846_) == 0)
{
lean_object* v_k_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_k_847_ = lean_ctor_get(v_p_846_, 0);
v___x_848_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_849_ = lean_int_dec_eq(v_k_847_, v___x_848_);
return v___x_849_;
}
else
{
uint8_t v___x_850_; 
v___x_850_ = 0;
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidEq___boxed(lean_object* v_p_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Int_Linear_Poly_isValidEq(v_p_851_);
lean_dec_ref(v_p_851_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter___redArg(lean_object* v_p_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_){
_start:
{
if (lean_obj_tag(v_p_854_) == 0)
{
lean_object* v_k_857_; lean_object* v___x_858_; 
lean_dec(v_h__2_856_);
v_k_857_ = lean_ctor_get(v_p_854_, 0);
lean_inc(v_k_857_);
lean_dec_ref(v_p_854_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_isUnsatEq_match__1_splitter(lean_object* v_motive_860_, lean_object* v_p_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_){
_start:
{
if (lean_obj_tag(v_p_861_) == 0)
{
lean_object* v_k_864_; lean_object* v___x_865_; 
lean_dec(v_h__2_863_);
v_k_864_ = lean_ctor_get(v_p_861_, 0);
lean_inc(v_k_864_);
lean_dec_ref(v_p_861_);
v___x_865_ = lean_apply_1(v_h__1_862_, v_k_864_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; 
lean_dec(v_h__1_862_);
v___x_866_ = lean_apply_2(v_h__2_863_, v_p_861_, lean_box(0));
return v___x_866_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object* v_p_867_){
_start:
{
if (lean_obj_tag(v_p_867_) == 0)
{
lean_object* v_k_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_k_868_ = lean_ctor_get(v_p_867_, 0);
v___x_869_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_870_ = lean_int_dec_lt(v___x_869_, v_k_868_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = 0;
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatLe___boxed(lean_object* v_p_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Int_Linear_Poly_isUnsatLe(v_p_872_);
lean_dec_ref(v_p_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isValidLe(lean_object* v_p_875_){
_start:
{
if (lean_obj_tag(v_p_875_) == 0)
{
lean_object* v_k_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_k_876_ = lean_ctor_get(v_p_875_, 0);
v___x_877_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_878_ = lean_int_dec_le(v_k_876_, v___x_877_);
return v___x_878_;
}
else
{
uint8_t v___x_879_; 
v___x_879_ = 0;
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isValidLe___boxed(lean_object* v_p_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Int_Linear_Poly_isValidLe(v_p_880_);
lean_dec_ref(v_p_880_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(lean_object* v_a_883_, lean_object* v_b_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Int_gcd(v_a_883_, v_b_884_);
v___x_886_ = lean_nat_to_int(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_gcd___boxed(lean_object* v_a_887_, lean_object* v_b_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Init_Data_Int_Linear_0__Int_Linear_gcd(v_a_887_, v_b_888_);
lean_dec(v_b_888_);
lean_dec(v_a_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
return v_x_891_;
}
else
{
lean_object* v_k_892_; lean_object* v_p_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_k_892_ = lean_ctor_get(v_x_890_, 0);
v_p_893_ = lean_ctor_get(v_x_890_, 2);
v___x_894_ = l_Int_gcd(v_k_892_, v_x_891_);
lean_dec(v_x_891_);
v___x_895_ = lean_nat_to_int(v___x_894_);
v_x_890_ = v_p_893_;
v_x_891_ = v___x_895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs___boxed(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Int_Linear_Poly_gcdCoeffs(v_x_897_, v_x_898_);
lean_dec_ref(v_x_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter___redArg(lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_h__1_902_, lean_object* v_h__2_903_){
_start:
{
if (lean_obj_tag(v_x_900_) == 0)
{
lean_object* v_k_904_; lean_object* v___x_905_; 
lean_dec(v_h__2_903_);
v_k_904_ = lean_ctor_get(v_x_900_, 0);
lean_inc(v_k_904_);
lean_dec_ref(v_x_900_);
v___x_905_ = lean_apply_2(v_h__1_902_, v_k_904_, v_x_901_);
return v___x_905_;
}
else
{
lean_object* v_k_906_; lean_object* v_v_907_; lean_object* v_p_908_; lean_object* v___x_909_; 
lean_dec(v_h__1_902_);
v_k_906_ = lean_ctor_get(v_x_900_, 0);
lean_inc(v_k_906_);
v_v_907_ = lean_ctor_get(v_x_900_, 1);
lean_inc(v_v_907_);
v_p_908_ = lean_ctor_get(v_x_900_, 2);
lean_inc_ref(v_p_908_);
lean_dec_ref(v_x_900_);
v___x_909_ = lean_apply_4(v_h__2_903_, v_k_906_, v_v_907_, v_p_908_, v_x_901_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_gcdCoeffs_match__1_splitter(lean_object* v_motive_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_h__1_913_, lean_object* v_h__2_914_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v_k_915_; lean_object* v___x_916_; 
lean_dec(v_h__2_914_);
v_k_915_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_k_915_);
lean_dec_ref(v_x_911_);
v___x_916_ = lean_apply_2(v_h__1_913_, v_k_915_, v_x_912_);
return v___x_916_;
}
else
{
lean_object* v_k_917_; lean_object* v_v_918_; lean_object* v_p_919_; lean_object* v___x_920_; 
lean_dec(v_h__1_913_);
v_k_917_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_k_917_);
v_v_918_ = lean_ctor_get(v_x_911_, 1);
lean_inc(v_v_918_);
v_p_919_ = lean_ctor_get(v_x_911_, 2);
lean_inc_ref(v_p_919_);
lean_dec_ref(v_x_911_);
v___x_920_ = lean_apply_4(v_h__2_914_, v_k_917_, v_v_918_, v_p_919_, v_x_912_);
return v___x_920_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object* v_k_921_, lean_object* v_p_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_923_ = l_Int_Linear_Poly_getConst(v_p_922_);
v___x_924_ = l_Int_Linear_Poly_gcdCoeffs(v_p_922_, v_k_921_);
v___x_925_ = lean_int_emod(v___x_923_, v___x_924_);
lean_dec(v___x_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_927_ = lean_int_dec_eq(v___x_925_, v___x_926_);
lean_dec(v___x_925_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = 1;
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDvd___boxed(lean_object* v_k_930_, lean_object* v_p_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Int_Linear_Poly_isUnsatDvd(v_k_930_, v_p_931_);
lean_dec_ref(v_p_931_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter___redArg(lean_object* v_p_u2081_934_, lean_object* v_p_u2082_935_, lean_object* v_h__1_936_, lean_object* v_h__2_937_){
_start:
{
if (lean_obj_tag(v_p_u2081_934_) == 1)
{
if (lean_obj_tag(v_p_u2082_935_) == 1)
{
lean_object* v_k_938_; lean_object* v_v_939_; lean_object* v_p_940_; lean_object* v_k_941_; lean_object* v_v_942_; lean_object* v_p_943_; lean_object* v___x_944_; 
lean_dec(v_h__2_937_);
v_k_938_ = lean_ctor_get(v_p_u2081_934_, 0);
lean_inc(v_k_938_);
v_v_939_ = lean_ctor_get(v_p_u2081_934_, 1);
lean_inc(v_v_939_);
v_p_940_ = lean_ctor_get(v_p_u2081_934_, 2);
lean_inc_ref(v_p_940_);
lean_dec_ref(v_p_u2081_934_);
v_k_941_ = lean_ctor_get(v_p_u2082_935_, 0);
lean_inc(v_k_941_);
v_v_942_ = lean_ctor_get(v_p_u2082_935_, 1);
lean_inc(v_v_942_);
v_p_943_ = lean_ctor_get(v_p_u2082_935_, 2);
lean_inc_ref(v_p_943_);
lean_dec_ref(v_p_u2082_935_);
v___x_944_ = lean_apply_6(v_h__1_936_, v_k_938_, v_v_939_, v_p_940_, v_k_941_, v_v_942_, v_p_943_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
lean_dec(v_h__1_936_);
v___x_945_ = lean_apply_3(v_h__2_937_, v_p_u2081_934_, v_p_u2082_935_, lean_box(0));
return v___x_945_;
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_h__1_936_);
v___x_946_ = lean_apply_3(v_h__2_937_, v_p_u2081_934_, v_p_u2082_935_, lean_box(0));
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_dvd__solve__elim__cert_match__1_splitter(lean_object* v_motive_947_, lean_object* v_p_u2081_948_, lean_object* v_p_u2082_949_, lean_object* v_h__1_950_, lean_object* v_h__2_951_){
_start:
{
if (lean_obj_tag(v_p_u2081_948_) == 1)
{
if (lean_obj_tag(v_p_u2082_949_) == 1)
{
lean_object* v_k_952_; lean_object* v_v_953_; lean_object* v_p_954_; lean_object* v_k_955_; lean_object* v_v_956_; lean_object* v_p_957_; lean_object* v___x_958_; 
lean_dec(v_h__2_951_);
v_k_952_ = lean_ctor_get(v_p_u2081_948_, 0);
lean_inc(v_k_952_);
v_v_953_ = lean_ctor_get(v_p_u2081_948_, 1);
lean_inc(v_v_953_);
v_p_954_ = lean_ctor_get(v_p_u2081_948_, 2);
lean_inc_ref(v_p_954_);
lean_dec_ref(v_p_u2081_948_);
v_k_955_ = lean_ctor_get(v_p_u2082_949_, 0);
lean_inc(v_k_955_);
v_v_956_ = lean_ctor_get(v_p_u2082_949_, 1);
lean_inc(v_v_956_);
v_p_957_ = lean_ctor_get(v_p_u2082_949_, 2);
lean_inc_ref(v_p_957_);
lean_dec_ref(v_p_u2082_949_);
v___x_958_ = lean_apply_6(v_h__1_950_, v_k_952_, v_v_953_, v_p_954_, v_k_955_, v_v_956_, v_p_957_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_h__1_950_);
v___x_959_ = lean_apply_3(v_h__2_951_, v_p_u2081_948_, v_p_u2082_949_, lean_box(0));
return v___x_959_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v_h__1_950_);
v___x_960_ = lean_apply_3(v_h__2_951_, v_p_u2081_948_, v_p_u2082_949_, lean_box(0));
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff(lean_object* v_p_961_){
_start:
{
if (lean_obj_tag(v_p_961_) == 1)
{
lean_object* v_k_962_; 
v_k_962_ = lean_ctor_get(v_p_961_, 0);
lean_inc(v_k_962_);
return v_k_962_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_leadCoeff___boxed(lean_object* v_p_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Int_Linear_Poly_leadCoeff(v_p_964_);
lean_dec_ref(v_p_964_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff(lean_object* v_p_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_p_966_) == 0)
{
lean_object* v___x_968_; 
v___x_968_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
return v___x_968_;
}
else
{
lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v_p_971_; uint8_t v___x_972_; 
v_k_969_ = lean_ctor_get(v_p_966_, 0);
v_v_970_ = lean_ctor_get(v_p_966_, 1);
v_p_971_ = lean_ctor_get(v_p_966_, 2);
v___x_972_ = lean_nat_dec_eq(v_x_967_, v_v_970_);
if (v___x_972_ == 0)
{
v_p_966_ = v_p_971_;
goto _start;
}
else
{
lean_inc(v_k_969_);
return v_k_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_coeff___boxed(lean_object* v_p_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Int_Linear_Poly_coeff(v_p_974_, v_x_975_);
lean_dec(v_x_975_);
lean_dec_ref(v_p_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter___redArg(lean_object* v_p_977_, lean_object* v_h__1_978_, lean_object* v_h__2_979_){
_start:
{
if (lean_obj_tag(v_p_977_) == 0)
{
lean_object* v_k_980_; lean_object* v___x_981_; 
lean_dec(v_h__1_978_);
v_k_980_ = lean_ctor_get(v_p_977_, 0);
lean_inc(v_k_980_);
lean_dec_ref(v_p_977_);
v___x_981_ = lean_apply_1(v_h__2_979_, v_k_980_);
return v___x_981_;
}
else
{
lean_object* v_k_982_; lean_object* v_v_983_; lean_object* v_p_984_; lean_object* v___x_985_; 
lean_dec(v_h__2_979_);
v_k_982_ = lean_ctor_get(v_p_977_, 0);
lean_inc(v_k_982_);
v_v_983_ = lean_ctor_get(v_p_977_, 1);
lean_inc(v_v_983_);
v_p_984_ = lean_ctor_get(v_p_977_, 2);
lean_inc_ref(v_p_984_);
lean_dec_ref(v_p_977_);
v___x_985_ = lean_apply_3(v_h__1_978_, v_k_982_, v_v_983_, v_p_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_coeff_match__1_splitter(lean_object* v_motive_986_, lean_object* v_p_987_, lean_object* v_h__1_988_, lean_object* v_h__2_989_){
_start:
{
if (lean_obj_tag(v_p_987_) == 0)
{
lean_object* v_k_990_; lean_object* v___x_991_; 
lean_dec(v_h__1_988_);
v_k_990_ = lean_ctor_get(v_p_987_, 0);
lean_inc(v_k_990_);
lean_dec_ref(v_p_987_);
v___x_991_ = lean_apply_1(v_h__2_989_, v_k_990_);
return v___x_991_;
}
else
{
lean_object* v_k_992_; lean_object* v_v_993_; lean_object* v_p_994_; lean_object* v___x_995_; 
lean_dec(v_h__2_989_);
v_k_992_ = lean_ctor_get(v_p_987_, 0);
lean_inc(v_k_992_);
v_v_993_ = lean_ctor_get(v_p_987_, 1);
lean_inc(v_v_993_);
v_p_994_ = lean_ctor_get(v_p_987_, 2);
lean_inc_ref(v_p_994_);
lean_dec_ref(v_p_987_);
v___x_995_ = lean_apply_3(v_h__1_988_, v_k_992_, v_v_993_, v_p_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_abs(lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_nat_abs(v_x_996_);
v___x_998_ = lean_nat_to_int(v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_abs___boxed(lean_object* v_x_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Int_Linear_abs(v_x_999_);
lean_dec(v_x_999_);
return v_res_1000_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isUnsatDiseq(lean_object* v_p_1001_){
_start:
{
if (lean_obj_tag(v_p_1001_) == 0)
{
lean_object* v_k_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_k_1002_ = lean_ctor_get(v_p_1001_, 0);
v___x_1003_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_1004_ = lean_int_dec_eq(v_k_1002_, v___x_1003_);
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = 0;
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isUnsatDiseq___boxed(lean_object* v_p_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Int_Linear_Poly_isUnsatDiseq(v_p_1006_);
lean_dec_ref(v_p_1006_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail(lean_object* v_p_1009_){
_start:
{
if (lean_obj_tag(v_p_1009_) == 1)
{
lean_object* v_p_1010_; 
v_p_1010_ = lean_ctor_get(v_p_1009_, 2);
lean_inc_ref(v_p_1010_);
return v_p_1010_;
}
else
{
lean_inc_ref(v_p_1009_);
return v_p_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_tail___boxed(lean_object* v_p_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Int_Linear_Poly_tail(v_p_1011_);
lean_dec_ref(v_p_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter___redArg(lean_object* v_p_1013_, lean_object* v_h__1_1014_, lean_object* v_h__2_1015_){
_start:
{
if (lean_obj_tag(v_p_1013_) == 1)
{
lean_object* v_k_1016_; lean_object* v_v_1017_; lean_object* v_p_1018_; lean_object* v___x_1019_; 
lean_dec(v_h__2_1015_);
v_k_1016_ = lean_ctor_get(v_p_1013_, 0);
lean_inc(v_k_1016_);
v_v_1017_ = lean_ctor_get(v_p_1013_, 1);
lean_inc(v_v_1017_);
v_p_1018_ = lean_ctor_get(v_p_1013_, 2);
lean_inc_ref(v_p_1018_);
lean_dec_ref(v_p_1013_);
v___x_1019_ = lean_apply_3(v_h__1_1014_, v_k_1016_, v_v_1017_, v_p_1018_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; 
lean_dec(v_h__1_1014_);
v___x_1020_ = lean_apply_2(v_h__2_1015_, v_p_1013_, lean_box(0));
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_Poly_leadCoeff_match__1_splitter(lean_object* v_motive_1021_, lean_object* v_p_1022_, lean_object* v_h__1_1023_, lean_object* v_h__2_1024_){
_start:
{
if (lean_obj_tag(v_p_1022_) == 1)
{
lean_object* v_k_1025_; lean_object* v_v_1026_; lean_object* v_p_1027_; lean_object* v___x_1028_; 
lean_dec(v_h__2_1024_);
v_k_1025_ = lean_ctor_get(v_p_1022_, 0);
lean_inc(v_k_1025_);
v_v_1026_ = lean_ctor_get(v_p_1022_, 1);
lean_inc(v_v_1026_);
v_p_1027_ = lean_ctor_get(v_p_1022_, 2);
lean_inc_ref(v_p_1027_);
lean_dec_ref(v_p_1022_);
v___x_1028_ = lean_apply_3(v_h__1_1023_, v_k_1025_, v_v_1026_, v_p_1027_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; 
lean_dec(v_h__1_1023_);
v___x_1029_ = lean_apply_2(v_h__2_1024_, v_p_1022_, lean_box(0));
return v___x_1029_;
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnAdd(lean_object* v_p_1030_, lean_object* v_k_1031_){
_start:
{
if (lean_obj_tag(v_p_1030_) == 0)
{
uint8_t v___x_1032_; 
lean_dec_ref(v_p_1030_);
lean_dec_ref(v_k_1031_);
v___x_1032_ = 0;
return v___x_1032_;
}
else
{
lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_a_1033_ = lean_ctor_get(v_p_1030_, 0);
lean_inc(v_a_1033_);
v_a_1034_ = lean_ctor_get(v_p_1030_, 1);
lean_inc(v_a_1034_);
v_a_1035_ = lean_ctor_get(v_p_1030_, 2);
lean_inc_ref(v_a_1035_);
lean_dec_ref(v_p_1030_);
v___x_1036_ = lean_apply_3(v_k_1031_, v_a_1033_, v_a_1034_, v_a_1035_);
v___x_1037_ = lean_unbox(v___x_1036_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnAdd___boxed(lean_object* v_p_1038_, lean_object* v_k_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Int_Linear_Poly_casesOnAdd(v_p_1038_, v_k_1039_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_casesOnNum(lean_object* v_p_1042_, lean_object* v_k_1043_){
_start:
{
if (lean_obj_tag(v_p_1042_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_a_1044_ = lean_ctor_get(v_p_1042_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v_p_1042_);
v___x_1045_ = lean_apply_1(v_k_1043_, v_a_1044_);
v___x_1046_ = lean_unbox(v___x_1045_);
return v___x_1046_;
}
else
{
uint8_t v___x_1047_; 
lean_dec_ref(v_p_1042_);
lean_dec_ref(v_k_1043_);
v___x_1047_ = 0;
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_casesOnNum___boxed(lean_object* v_p_1048_, lean_object* v_k_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l_Int_Linear_Poly_casesOnNum(v_p_1048_, v_k_1049_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_emod__le__cert(lean_object* v_y_1052_, lean_object* v_n_1053_){
_start:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_obj_once(&l_Int_Linear_instInhabitedExpr_default___closed__0, &l_Int_Linear_instInhabitedExpr_default___closed__0_once, _init_l_Int_Linear_instInhabitedExpr_default___closed__0);
v___x_1055_ = lean_int_dec_eq(v_y_1052_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1056_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
v___x_1057_ = lean_nat_abs(v_y_1052_);
v___x_1058_ = lean_nat_to_int(v___x_1057_);
v___x_1059_ = lean_int_sub(v___x_1056_, v___x_1058_);
lean_dec(v___x_1058_);
v___x_1060_ = lean_int_dec_eq(v_n_1053_, v___x_1059_);
lean_dec(v___x_1059_);
return v___x_1060_;
}
else
{
uint8_t v___x_1061_; 
v___x_1061_ = 0;
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_emod__le__cert___boxed(lean_object* v_y_1062_, lean_object* v_n_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Int_Linear_emod__le__cert(v_y_1062_, v_n_1063_);
lean_dec(v_n_1063_);
lean_dec(v_y_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_le__of__le__cert(lean_object* v_p_u2081_1066_, lean_object* v_p_u2082_1067_){
_start:
{
if (lean_obj_tag(v_p_u2081_1066_) == 0)
{
if (lean_obj_tag(v_p_u2082_1067_) == 0)
{
lean_object* v_k_1068_; lean_object* v_k_1069_; uint8_t v___x_1070_; 
v_k_1068_ = lean_ctor_get(v_p_u2081_1066_, 0);
v_k_1069_ = lean_ctor_get(v_p_u2082_1067_, 0);
v___x_1070_ = lean_int_dec_le(v_k_1069_, v_k_1068_);
return v___x_1070_;
}
else
{
uint8_t v___x_1071_; 
v___x_1071_ = 0;
return v___x_1071_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1067_) == 0)
{
uint8_t v___x_1072_; 
v___x_1072_ = 0;
return v___x_1072_;
}
else
{
lean_object* v_k_1073_; lean_object* v_v_1074_; lean_object* v_p_1075_; lean_object* v_k_1076_; lean_object* v_v_1077_; lean_object* v_p_1078_; uint8_t v___y_1080_; uint8_t v___x_1082_; 
v_k_1073_ = lean_ctor_get(v_p_u2081_1066_, 0);
v_v_1074_ = lean_ctor_get(v_p_u2081_1066_, 1);
v_p_1075_ = lean_ctor_get(v_p_u2081_1066_, 2);
v_k_1076_ = lean_ctor_get(v_p_u2082_1067_, 0);
v_v_1077_ = lean_ctor_get(v_p_u2082_1067_, 1);
v_p_1078_ = lean_ctor_get(v_p_u2082_1067_, 2);
v___x_1082_ = lean_int_dec_eq(v_k_1073_, v_k_1076_);
if (v___x_1082_ == 0)
{
v___y_1080_ = v___x_1082_;
goto v___jp_1079_;
}
else
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_eq(v_v_1074_, v_v_1077_);
v___y_1080_ = v___x_1083_;
goto v___jp_1079_;
}
v___jp_1079_:
{
if (v___y_1080_ == 0)
{
return v___y_1080_;
}
else
{
v_p_u2081_1066_ = v_p_1075_;
v_p_u2082_1067_ = v_p_1078_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_le__of__le__cert___boxed(lean_object* v_p_u2081_1084_, lean_object* v_p_u2082_1085_){
_start:
{
uint8_t v_res_1086_; lean_object* v_r_1087_; 
v_res_1086_ = l_Int_Linear_le__of__le__cert(v_p_u2081_1084_, v_p_u2082_1085_);
lean_dec_ref(v_p_u2082_1085_);
lean_dec_ref(v_p_u2081_1084_);
v_r_1087_ = lean_box(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter___redArg(lean_object* v_p_u2081_1088_, lean_object* v_p_u2082_1089_, lean_object* v_h__1_1090_, lean_object* v_h__2_1091_, lean_object* v_h__3_1092_, lean_object* v_h__4_1093_){
_start:
{
if (lean_obj_tag(v_p_u2081_1088_) == 0)
{
lean_dec(v_h__4_1093_);
lean_dec(v_h__1_1090_);
if (lean_obj_tag(v_p_u2082_1089_) == 0)
{
lean_object* v_k_1094_; lean_object* v_k_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__2_1091_);
v_k_1094_ = lean_ctor_get(v_p_u2081_1088_, 0);
lean_inc(v_k_1094_);
lean_dec_ref(v_p_u2081_1088_);
v_k_1095_ = lean_ctor_get(v_p_u2082_1089_, 0);
lean_inc(v_k_1095_);
lean_dec_ref(v_p_u2082_1089_);
v___x_1096_ = lean_apply_2(v_h__3_1092_, v_k_1094_, v_k_1095_);
return v___x_1096_;
}
else
{
lean_object* v_k_1097_; lean_object* v_k_1098_; lean_object* v_v_1099_; lean_object* v_p_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__3_1092_);
v_k_1097_ = lean_ctor_get(v_p_u2081_1088_, 0);
lean_inc(v_k_1097_);
lean_dec_ref(v_p_u2081_1088_);
v_k_1098_ = lean_ctor_get(v_p_u2082_1089_, 0);
lean_inc(v_k_1098_);
v_v_1099_ = lean_ctor_get(v_p_u2082_1089_, 1);
lean_inc(v_v_1099_);
v_p_1100_ = lean_ctor_get(v_p_u2082_1089_, 2);
lean_inc_ref(v_p_1100_);
lean_dec_ref(v_p_u2082_1089_);
v___x_1101_ = lean_apply_4(v_h__2_1091_, v_k_1097_, v_k_1098_, v_v_1099_, v_p_1100_);
return v___x_1101_;
}
}
else
{
lean_dec(v_h__3_1092_);
lean_dec(v_h__2_1091_);
if (lean_obj_tag(v_p_u2082_1089_) == 0)
{
lean_object* v_k_1102_; lean_object* v_v_1103_; lean_object* v_p_1104_; lean_object* v_k_1105_; lean_object* v___x_1106_; 
lean_dec(v_h__4_1093_);
v_k_1102_ = lean_ctor_get(v_p_u2081_1088_, 0);
lean_inc(v_k_1102_);
v_v_1103_ = lean_ctor_get(v_p_u2081_1088_, 1);
lean_inc(v_v_1103_);
v_p_1104_ = lean_ctor_get(v_p_u2081_1088_, 2);
lean_inc_ref(v_p_1104_);
lean_dec_ref(v_p_u2081_1088_);
v_k_1105_ = lean_ctor_get(v_p_u2082_1089_, 0);
lean_inc(v_k_1105_);
lean_dec_ref(v_p_u2082_1089_);
v___x_1106_ = lean_apply_4(v_h__1_1090_, v_k_1102_, v_v_1103_, v_p_1104_, v_k_1105_);
return v___x_1106_;
}
else
{
lean_object* v_k_1107_; lean_object* v_v_1108_; lean_object* v_p_1109_; lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v_p_1112_; lean_object* v___x_1113_; 
lean_dec(v_h__1_1090_);
v_k_1107_ = lean_ctor_get(v_p_u2081_1088_, 0);
lean_inc(v_k_1107_);
v_v_1108_ = lean_ctor_get(v_p_u2081_1088_, 1);
lean_inc(v_v_1108_);
v_p_1109_ = lean_ctor_get(v_p_u2081_1088_, 2);
lean_inc_ref(v_p_1109_);
lean_dec_ref(v_p_u2081_1088_);
v_k_1110_ = lean_ctor_get(v_p_u2082_1089_, 0);
lean_inc(v_k_1110_);
v_v_1111_ = lean_ctor_get(v_p_u2082_1089_, 1);
lean_inc(v_v_1111_);
v_p_1112_ = lean_ctor_get(v_p_u2082_1089_, 2);
lean_inc_ref(v_p_1112_);
lean_dec_ref(v_p_u2082_1089_);
v___x_1113_ = lean_apply_6(v_h__4_1093_, v_k_1107_, v_v_1108_, v_p_1109_, v_k_1110_, v_v_1111_, v_p_1112_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Linear_0__Int_Linear_le__of__le__cert_match__1_splitter(lean_object* v_motive_1114_, lean_object* v_p_u2081_1115_, lean_object* v_p_u2082_1116_, lean_object* v_h__1_1117_, lean_object* v_h__2_1118_, lean_object* v_h__3_1119_, lean_object* v_h__4_1120_){
_start:
{
if (lean_obj_tag(v_p_u2081_1115_) == 0)
{
lean_dec(v_h__4_1120_);
lean_dec(v_h__1_1117_);
if (lean_obj_tag(v_p_u2082_1116_) == 0)
{
lean_object* v_k_1121_; lean_object* v_k_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__2_1118_);
v_k_1121_ = lean_ctor_get(v_p_u2081_1115_, 0);
lean_inc(v_k_1121_);
lean_dec_ref(v_p_u2081_1115_);
v_k_1122_ = lean_ctor_get(v_p_u2082_1116_, 0);
lean_inc(v_k_1122_);
lean_dec_ref(v_p_u2082_1116_);
v___x_1123_ = lean_apply_2(v_h__3_1119_, v_k_1121_, v_k_1122_);
return v___x_1123_;
}
else
{
lean_object* v_k_1124_; lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v_p_1127_; lean_object* v___x_1128_; 
lean_dec(v_h__3_1119_);
v_k_1124_ = lean_ctor_get(v_p_u2081_1115_, 0);
lean_inc(v_k_1124_);
lean_dec_ref(v_p_u2081_1115_);
v_k_1125_ = lean_ctor_get(v_p_u2082_1116_, 0);
lean_inc(v_k_1125_);
v_v_1126_ = lean_ctor_get(v_p_u2082_1116_, 1);
lean_inc(v_v_1126_);
v_p_1127_ = lean_ctor_get(v_p_u2082_1116_, 2);
lean_inc_ref(v_p_1127_);
lean_dec_ref(v_p_u2082_1116_);
v___x_1128_ = lean_apply_4(v_h__2_1118_, v_k_1124_, v_k_1125_, v_v_1126_, v_p_1127_);
return v___x_1128_;
}
}
else
{
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
if (lean_obj_tag(v_p_u2082_1116_) == 0)
{
lean_object* v_k_1129_; lean_object* v_v_1130_; lean_object* v_p_1131_; lean_object* v_k_1132_; lean_object* v___x_1133_; 
lean_dec(v_h__4_1120_);
v_k_1129_ = lean_ctor_get(v_p_u2081_1115_, 0);
lean_inc(v_k_1129_);
v_v_1130_ = lean_ctor_get(v_p_u2081_1115_, 1);
lean_inc(v_v_1130_);
v_p_1131_ = lean_ctor_get(v_p_u2081_1115_, 2);
lean_inc_ref(v_p_1131_);
lean_dec_ref(v_p_u2081_1115_);
v_k_1132_ = lean_ctor_get(v_p_u2082_1116_, 0);
lean_inc(v_k_1132_);
lean_dec_ref(v_p_u2082_1116_);
v___x_1133_ = lean_apply_4(v_h__1_1117_, v_k_1129_, v_v_1130_, v_p_1131_, v_k_1132_);
return v___x_1133_;
}
else
{
lean_object* v_k_1134_; lean_object* v_v_1135_; lean_object* v_p_1136_; lean_object* v_k_1137_; lean_object* v_v_1138_; lean_object* v_p_1139_; lean_object* v___x_1140_; 
lean_dec(v_h__1_1117_);
v_k_1134_ = lean_ctor_get(v_p_u2081_1115_, 0);
lean_inc(v_k_1134_);
v_v_1135_ = lean_ctor_get(v_p_u2081_1115_, 1);
lean_inc(v_v_1135_);
v_p_1136_ = lean_ctor_get(v_p_u2081_1115_, 2);
lean_inc_ref(v_p_1136_);
lean_dec_ref(v_p_u2081_1115_);
v_k_1137_ = lean_ctor_get(v_p_u2082_1116_, 0);
lean_inc(v_k_1137_);
v_v_1138_ = lean_ctor_get(v_p_u2082_1116_, 1);
lean_inc(v_v_1138_);
v_p_1139_ = lean_ctor_get(v_p_u2082_1116_, 2);
lean_inc_ref(v_p_1139_);
lean_dec_ref(v_p_u2082_1116_);
v___x_1140_ = lean_apply_6(v_h__4_1120_, v_k_1134_, v_v_1135_, v_p_1136_, v_k_1137_, v_v_1138_, v_p_1139_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT uint8_t l_Int_Linear_not__le__of__le__cert(lean_object* v_p_u2081_1141_, lean_object* v_p_u2082_1142_){
_start:
{
if (lean_obj_tag(v_p_u2081_1141_) == 0)
{
if (lean_obj_tag(v_p_u2082_1142_) == 0)
{
lean_object* v_k_1143_; lean_object* v_k_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_k_1143_ = lean_ctor_get(v_p_u2081_1141_, 0);
v_k_1144_ = lean_ctor_get(v_p_u2082_1142_, 0);
v___x_1145_ = lean_obj_once(&l_Int_Linear_Expr_toPoly_x27___closed__0, &l_Int_Linear_Expr_toPoly_x27___closed__0_once, _init_l_Int_Linear_Expr_toPoly_x27___closed__0);
v___x_1146_ = lean_int_sub(v___x_1145_, v_k_1144_);
v___x_1147_ = lean_int_dec_le(v___x_1146_, v_k_1143_);
lean_dec(v___x_1146_);
return v___x_1147_;
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = 0;
return v___x_1148_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_1142_) == 0)
{
uint8_t v___x_1149_; 
v___x_1149_ = 0;
return v___x_1149_;
}
else
{
lean_object* v_k_1150_; lean_object* v_v_1151_; lean_object* v_p_1152_; lean_object* v_k_1153_; lean_object* v_v_1154_; lean_object* v_p_1155_; uint8_t v___y_1157_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_k_1150_ = lean_ctor_get(v_p_u2081_1141_, 0);
v_v_1151_ = lean_ctor_get(v_p_u2081_1141_, 1);
v_p_1152_ = lean_ctor_get(v_p_u2081_1141_, 2);
v_k_1153_ = lean_ctor_get(v_p_u2082_1142_, 0);
v_v_1154_ = lean_ctor_get(v_p_u2082_1142_, 1);
v_p_1155_ = lean_ctor_get(v_p_u2082_1142_, 2);
v___x_1159_ = lean_int_neg(v_k_1153_);
v___x_1160_ = lean_int_dec_eq(v_k_1150_, v___x_1159_);
lean_dec(v___x_1159_);
if (v___x_1160_ == 0)
{
v___y_1157_ = v___x_1160_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_eq(v_v_1151_, v_v_1154_);
v___y_1157_ = v___x_1161_;
goto v___jp_1156_;
}
v___jp_1156_:
{
if (v___y_1157_ == 0)
{
return v___y_1157_;
}
else
{
v_p_u2081_1141_ = v_p_1152_;
v_p_u2082_1142_ = v_p_1155_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_not__le__of__le__cert___boxed(lean_object* v_p_u2081_1162_, lean_object* v_p_u2082_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Int_Linear_not__le__of__le__cert(v_p_u2081_1162_, v_p_u2082_1163_);
lean_dec_ref(v_p_u2082_1163_);
lean_dec_ref(v_p_u2081_1162_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
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
