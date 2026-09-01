// Lean compiler output
// Module: Init.Data.Nat.Internal.Linear
// Imports: public import Init.Data.RArray import Init.LawfulBEqTactics import Init.ByCases import Init.Data.Prod import Init.Data.Bool
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_fixedVar;
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulL_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulL_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Internal_Linear_instInhabitedExpr_default = (const lean_object*)&l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Internal_Linear_instInhabitedExpr = (const lean_object*)&l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_Internal_Linear_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_Internal_Linear_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_Internal_Linear_instBEqExpr___closed__0 = (const lean_object*)&l_Nat_Internal_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Internal_Linear_instBEqExpr = (const lean_object*)&l_Nat_Internal_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_hugeFuel;
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancel(lean_object*, lean_object*);
static const lean_ctor_object l_Nat_Internal_Linear_Poly_isNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f___closed__0 = (const lean_object*)&l_Nat_Internal_Linear_Poly_isNum_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_Poly_isNonZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNonZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly___boxed(lean_object*);
static const lean_ctor_object l_Nat_Internal_Linear_Expr_inc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Nat_Internal_Linear_Expr_inc___closed__0 = (const lean_object*)&l_Nat_Internal_Linear_Expr_inc___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_inc(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_instBEqPolyCnstr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqPolyCnstr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_Internal_Linear_instBEqPolyCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_Internal_Linear_instBEqPolyCnstr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_Internal_Linear_instBEqPolyCnstr___closed__0 = (const lean_object*)&l_Nat_Internal_Linear_instBEqPolyCnstr___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Internal_Linear_instBEqPolyCnstr = (const lean_object*)&l_Nat_Internal_Linear_instBEqPolyCnstr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_norm(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_PolyCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_PolyCnstr_isValid(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isValid___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_monomialToExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_Internal_Linear_fixedVar(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(100000000u);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx(lean_object* v_x_2_){
_start:
{
switch(lean_obj_tag(v_x_2_))
{
case 0:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(0u);
return v___x_3_;
}
case 1:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(1u);
return v___x_4_;
}
case 2:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(2u);
return v___x_5_;
}
case 3:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(3u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(4u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Nat_Internal_Linear_Expr_ctorIdx(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
switch(lean_obj_tag(v_t_10_))
{
case 2:
{
lean_object* v_a_12_; lean_object* v_b_13_; lean_object* v___x_14_; 
v_a_12_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_a_12_);
v_b_13_ = lean_ctor_get(v_t_10_, 1);
lean_inc_ref(v_b_13_);
lean_dec_ref_known(v_t_10_, 2);
v___x_14_ = lean_apply_2(v_k_11_, v_a_12_, v_b_13_);
return v___x_14_;
}
case 3:
{
lean_object* v_k_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_k_15_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_k_15_);
v_a_16_ = lean_ctor_get(v_t_10_, 1);
lean_inc_ref(v_a_16_);
lean_dec_ref_known(v_t_10_, 2);
v___x_17_ = lean_apply_2(v_k_11_, v_k_15_, v_a_16_);
return v___x_17_;
}
case 4:
{
lean_object* v_a_18_; lean_object* v_k_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_a_18_);
v_k_19_ = lean_ctor_get(v_t_10_, 1);
lean_inc(v_k_19_);
lean_dec_ref_known(v_t_10_, 2);
v___x_20_ = lean_apply_2(v_k_11_, v_a_18_, v_k_19_);
return v___x_20_;
}
default: 
{
lean_object* v_v_21_; lean_object* v___x_22_; 
v_v_21_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_v_21_);
lean_dec_ref(v_t_10_);
v___x_22_ = lean_apply_1(v_k_11_, v_v_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_25_, v_k_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim___boxed(lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Nat_Internal_Linear_Expr_ctorElim(v_motive_29_, v_ctorIdx_30_, v_t_31_, v_h_32_, v_k_33_);
lean_dec(v_ctorIdx_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_num_elim___redArg(lean_object* v_t_35_, lean_object* v_num_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_35_, v_num_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_num_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_num_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_39_, v_num_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_var_elim___redArg(lean_object* v_t_43_, lean_object* v_var_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_43_, v_var_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_var_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_var_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_47_, v_var_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_add_elim___redArg(lean_object* v_t_51_, lean_object* v_add_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_51_, v_add_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_add_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_add_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_55_, v_add_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulL_elim___redArg(lean_object* v_t_59_, lean_object* v_mulL_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_59_, v_mulL_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulL_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_mulL_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_63_, v_mulL_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulR_elim___redArg(lean_object* v_t_67_, lean_object* v_mulR_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_67_, v_mulR_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulR_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_mulR_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_71_, v_mulR_73_);
return v___x_74_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_instBEqExpr_beq(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
switch(lean_obj_tag(v_x_79_))
{
case 0:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_v_81_; lean_object* v_v_82_; uint8_t v___x_83_; 
v_v_81_ = lean_ctor_get(v_x_79_, 0);
v_v_82_ = lean_ctor_get(v_x_80_, 0);
v___x_83_ = lean_nat_dec_eq(v_v_81_, v_v_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
case 1:
{
if (lean_obj_tag(v_x_80_) == 1)
{
lean_object* v_i_85_; lean_object* v_i_86_; uint8_t v___x_87_; 
v_i_85_ = lean_ctor_get(v_x_79_, 0);
v_i_86_ = lean_ctor_get(v_x_80_, 0);
v___x_87_ = lean_nat_dec_eq(v_i_85_, v_i_86_);
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
case 2:
{
if (lean_obj_tag(v_x_80_) == 2)
{
lean_object* v_a_89_; lean_object* v_b_90_; lean_object* v_a_91_; lean_object* v_b_92_; uint8_t v___x_93_; 
v_a_89_ = lean_ctor_get(v_x_79_, 0);
v_b_90_ = lean_ctor_get(v_x_79_, 1);
v_a_91_ = lean_ctor_get(v_x_80_, 0);
v_b_92_ = lean_ctor_get(v_x_80_, 1);
v___x_93_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_a_89_, v_a_91_);
if (v___x_93_ == 0)
{
return v___x_93_;
}
else
{
v_x_79_ = v_b_90_;
v_x_80_ = v_b_92_;
goto _start;
}
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
case 3:
{
if (lean_obj_tag(v_x_80_) == 3)
{
lean_object* v_k_96_; lean_object* v_a_97_; lean_object* v_k_98_; lean_object* v_a_99_; uint8_t v___x_100_; 
v_k_96_ = lean_ctor_get(v_x_79_, 0);
v_a_97_ = lean_ctor_get(v_x_79_, 1);
v_k_98_ = lean_ctor_get(v_x_80_, 0);
v_a_99_ = lean_ctor_get(v_x_80_, 1);
v___x_100_ = lean_nat_dec_eq(v_k_96_, v_k_98_);
if (v___x_100_ == 0)
{
return v___x_100_;
}
else
{
v_x_79_ = v_a_97_;
v_x_80_ = v_a_99_;
goto _start;
}
}
else
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
}
default: 
{
if (lean_obj_tag(v_x_80_) == 4)
{
lean_object* v_a_103_; lean_object* v_k_104_; lean_object* v_a_105_; lean_object* v_k_106_; uint8_t v___x_107_; 
v_a_103_ = lean_ctor_get(v_x_79_, 0);
v_k_104_ = lean_ctor_get(v_x_79_, 1);
v_a_105_ = lean_ctor_get(v_x_80_, 0);
v_k_106_ = lean_ctor_get(v_x_80_, 1);
v___x_107_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_a_103_, v_a_105_);
if (v___x_107_ == 0)
{
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_eq(v_k_104_, v_k_106_);
return v___x_108_;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqExpr_beq___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_x_110_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec_ref(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_insert(lean_object* v_k_116_, lean_object* v_v_117_, lean_object* v_p_118_){
_start:
{
if (lean_obj_tag(v_p_118_) == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_k_116_);
lean_ctor_set(v___x_119_, 1, v_v_117_);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_p_118_);
return v___x_120_;
}
else
{
lean_object* v_head_121_; lean_object* v_tail_122_; lean_object* v_fst_123_; lean_object* v_snd_124_; uint8_t v___x_125_; 
v_head_121_ = lean_ctor_get(v_p_118_, 0);
lean_inc(v_head_121_);
v_tail_122_ = lean_ctor_get(v_p_118_, 1);
v_fst_123_ = lean_ctor_get(v_head_121_, 0);
v_snd_124_ = lean_ctor_get(v_head_121_, 1);
v___x_125_ = l_Nat_blt(v_v_117_, v_snd_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_147_; 
lean_inc(v_tail_122_);
v_isSharedCheck_147_ = !lean_is_exclusive(v_p_118_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; lean_object* v_unused_149_; 
v_unused_148_ = lean_ctor_get(v_p_118_, 1);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_p_118_, 0);
lean_dec(v_unused_149_);
v___x_127_ = v_p_118_;
v_isShared_128_ = v_isSharedCheck_147_;
goto v_resetjp_126_;
}
else
{
lean_dec(v_p_118_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_147_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_eq(v_v_117_, v_snd_124_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = l_Nat_Internal_Linear_Poly_insert(v_k_116_, v_v_117_, v_tail_122_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_130_);
v___x_132_ = v___x_127_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_head_121_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_144_; 
lean_inc(v_snd_124_);
lean_inc(v_fst_123_);
lean_dec(v_v_117_);
v_isSharedCheck_144_ = !lean_is_exclusive(v_head_121_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_145_ = lean_ctor_get(v_head_121_, 1);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_head_121_, 0);
lean_dec(v_unused_146_);
v___x_135_ = v_head_121_;
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_head_121_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_nat_add(v_k_116_, v_fst_123_);
lean_dec(v_fst_123_);
lean_dec(v_k_116_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_snd_124_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_139_);
v___x_141_ = v___x_127_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_tail_122_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
else
{
lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_isSharedCheck_157_ = !lean_is_exclusive(v_head_121_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; 
v_unused_158_ = lean_ctor_get(v_head_121_, 1);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_head_121_, 0);
lean_dec(v_unused_159_);
v___x_151_ = v_head_121_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_dec(v_head_121_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_v_117_);
lean_ctor_set(v___x_151_, 0, v_k_116_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_k_116_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_v_117_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_p_118_);
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm_go(lean_object* v_p_160_, lean_object* v_r_161_){
_start:
{
if (lean_obj_tag(v_p_160_) == 0)
{
return v_r_161_;
}
else
{
lean_object* v_head_162_; lean_object* v_tail_163_; lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v___x_166_; 
v_head_162_ = lean_ctor_get(v_p_160_, 0);
lean_inc(v_head_162_);
v_tail_163_ = lean_ctor_get(v_p_160_, 1);
lean_inc(v_tail_163_);
lean_dec_ref_known(v_p_160_, 2);
v_fst_164_ = lean_ctor_get(v_head_162_, 0);
lean_inc(v_fst_164_);
v_snd_165_ = lean_ctor_get(v_head_162_, 1);
lean_inc(v_snd_165_);
lean_dec(v_head_162_);
v___x_166_ = l_Nat_Internal_Linear_Poly_insert(v_fst_164_, v_snd_165_, v_r_161_);
v_p_160_ = v_tail_163_;
v_r_161_ = v___x_166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm(lean_object* v_p_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_box(0);
v___x_170_ = l_Nat_Internal_Linear_Poly_norm_go(v_p_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancelAux(lean_object* v_fuel_171_, lean_object* v_m_u2081_172_, lean_object* v_m_u2082_173_, lean_object* v_r_u2081_174_, lean_object* v_r_u2082_175_){
_start:
{
lean_object* v_zero_176_; uint8_t v_isZero_177_; 
v_zero_176_ = lean_unsigned_to_nat(0u);
v_isZero_177_ = lean_nat_dec_eq(v_fuel_171_, v_zero_176_);
if (v_isZero_177_ == 1)
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_fuel_171_);
v___x_178_ = l_List_reverse___redArg(v_r_u2081_174_);
v___x_179_ = l_List_appendTR___redArg(v___x_178_, v_m_u2081_172_);
v___x_180_ = l_List_reverse___redArg(v_r_u2082_175_);
v___x_181_ = l_List_appendTR___redArg(v___x_180_, v_m_u2082_173_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
else
{
if (lean_obj_tag(v_m_u2082_173_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_fuel_171_);
v___x_183_ = l_List_reverse___redArg(v_r_u2081_174_);
v___x_184_ = l_List_appendTR___redArg(v___x_183_, v_m_u2081_172_);
v___x_185_ = l_List_reverse___redArg(v_r_u2082_175_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
return v___x_186_;
}
else
{
if (lean_obj_tag(v_m_u2081_172_) == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_fuel_171_);
v___x_187_ = l_List_reverse___redArg(v_r_u2081_174_);
v___x_188_ = l_List_reverse___redArg(v_r_u2082_175_);
v___x_189_ = l_List_appendTR___redArg(v___x_188_, v_m_u2082_173_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_187_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_head_191_; lean_object* v_head_192_; lean_object* v_tail_193_; lean_object* v_tail_194_; lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v_one_199_; lean_object* v_n_200_; uint8_t v___x_201_; 
v_head_191_ = lean_ctor_get(v_m_u2081_172_, 0);
v_head_192_ = lean_ctor_get(v_m_u2082_173_, 0);
lean_inc(v_head_192_);
v_tail_193_ = lean_ctor_get(v_m_u2082_173_, 1);
v_tail_194_ = lean_ctor_get(v_m_u2081_172_, 1);
v_fst_195_ = lean_ctor_get(v_head_191_, 0);
v_snd_196_ = lean_ctor_get(v_head_191_, 1);
v_fst_197_ = lean_ctor_get(v_head_192_, 0);
v_snd_198_ = lean_ctor_get(v_head_192_, 1);
v_one_199_ = lean_unsigned_to_nat(1u);
v_n_200_ = lean_nat_sub(v_fuel_171_, v_one_199_);
lean_dec(v_fuel_171_);
v___x_201_ = l_Nat_blt(v_snd_196_, v_snd_198_);
if (v___x_201_ == 0)
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_241_; 
lean_inc(v_tail_193_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_m_u2082_173_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; 
v_unused_242_ = lean_ctor_get(v_m_u2082_173_, 1);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_m_u2082_173_, 0);
lean_dec(v_unused_243_);
v___x_203_ = v_m_u2082_173_;
v_isShared_204_ = v_isSharedCheck_241_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_m_u2082_173_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_241_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; 
v___x_205_ = l_Nat_blt(v_snd_198_, v_snd_196_);
if (v___x_205_ == 0)
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_234_; 
lean_inc(v_fst_197_);
lean_inc(v_snd_196_);
lean_inc(v_fst_195_);
lean_inc(v_tail_194_);
lean_del_object(v___x_203_);
v_isSharedCheck_234_ = !lean_is_exclusive(v_m_u2081_172_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; lean_object* v_unused_236_; 
v_unused_235_ = lean_ctor_get(v_m_u2081_172_, 1);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_m_u2081_172_, 0);
lean_dec(v_unused_236_);
v___x_207_ = v_m_u2081_172_;
v_isShared_208_ = v_isSharedCheck_234_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_m_u2081_172_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_234_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_231_; 
v_isSharedCheck_231_ = !lean_is_exclusive(v_head_192_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_232_ = lean_ctor_get(v_head_192_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_head_192_, 0);
lean_dec(v_unused_233_);
v___x_210_ = v_head_192_;
v_isShared_211_ = v_isSharedCheck_231_;
goto v_resetjp_209_;
}
else
{
lean_dec(v_head_192_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_231_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint8_t v___x_212_; 
v___x_212_ = l_Nat_blt(v_fst_195_, v_fst_197_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
v___x_213_ = l_Nat_blt(v_fst_197_, v_fst_195_);
if (v___x_213_ == 0)
{
lean_del_object(v___x_210_);
lean_del_object(v___x_207_);
lean_dec(v_fst_197_);
lean_dec(v_snd_196_);
lean_dec(v_fst_195_);
v_fuel_171_ = v_n_200_;
v_m_u2081_172_ = v_tail_194_;
v_m_u2082_173_ = v_tail_193_;
goto _start;
}
else
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_nat_sub(v_fst_195_, v_fst_197_);
lean_dec(v_fst_197_);
lean_dec(v_fst_195_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_snd_196_);
lean_ctor_set(v___x_210_, 0, v___x_215_);
v___x_217_ = v___x_210_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_snd_196_);
v___x_217_ = v_reuseFailAlloc_222_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_r_u2081_174_);
lean_ctor_set(v___x_207_, 0, v___x_217_);
v___x_219_ = v___x_207_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_r_u2081_174_);
v___x_219_ = v_reuseFailAlloc_221_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v_fuel_171_ = v_n_200_;
v_m_u2081_172_ = v_tail_194_;
v_m_u2082_173_ = v_tail_193_;
v_r_u2081_174_ = v___x_219_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_nat_sub(v_fst_197_, v_fst_195_);
lean_dec(v_fst_195_);
lean_dec(v_fst_197_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_snd_196_);
lean_ctor_set(v___x_210_, 0, v___x_223_);
v___x_225_ = v___x_210_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_snd_196_);
v___x_225_ = v_reuseFailAlloc_230_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_r_u2082_175_);
lean_ctor_set(v___x_207_, 0, v___x_225_);
v___x_227_ = v___x_207_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_r_u2082_175_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
v_fuel_171_ = v_n_200_;
v_m_u2081_172_ = v_tail_194_;
v_m_u2082_173_ = v_tail_193_;
v_r_u2082_175_ = v___x_227_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_238_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_r_u2082_175_);
v___x_238_ = v___x_203_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_head_192_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_r_u2082_175_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
v_fuel_171_ = v_n_200_;
v_m_u2082_173_ = v_tail_193_;
v_r_u2082_175_ = v___x_238_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
lean_inc(v_tail_194_);
lean_inc(v_head_191_);
lean_dec(v_head_192_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_m_u2081_172_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_252_ = lean_ctor_get(v_m_u2081_172_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_m_u2081_172_, 0);
lean_dec(v_unused_253_);
v___x_245_ = v_m_u2081_172_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_m_u2081_172_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_r_u2081_174_);
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_head_191_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_r_u2081_174_);
v___x_248_ = v_reuseFailAlloc_250_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v_fuel_171_ = v_n_200_;
v_m_u2081_172_ = v_tail_194_;
v_r_u2081_174_ = v___x_248_;
goto _start;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Nat_Internal_Linear_hugeFuel(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_unsigned_to_nat(1000000u);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancel(lean_object* v_p_u2081_255_, lean_object* v_p_u2082_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(1000000u);
v___x_258_ = lean_box(0);
v___x_259_ = l_Nat_Internal_Linear_Poly_cancelAux(v___x_257_, v_p_u2081_255_, v_p_u2082_256_, v___x_258_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f(lean_object* v_p_262_){
_start:
{
if (lean_obj_tag(v_p_262_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l_Nat_Internal_Linear_Poly_isNum_x3f___closed__0));
return v___x_263_;
}
else
{
lean_object* v_tail_264_; 
v_tail_264_ = lean_ctor_get(v_p_262_, 1);
if (lean_obj_tag(v_tail_264_) == 0)
{
lean_object* v_head_265_; lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_head_265_ = lean_ctor_get(v_p_262_, 0);
v_fst_266_ = lean_ctor_get(v_head_265_, 0);
v_snd_267_ = lean_ctor_get(v_head_265_, 1);
v___x_268_ = lean_unsigned_to_nat(100000000u);
v___x_269_ = lean_nat_dec_eq(v_snd_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
lean_inc(v_fst_266_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_fst_266_);
return v___x_271_;
}
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f___boxed(lean_object* v_p_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Nat_Internal_Linear_Poly_isNum_x3f(v_p_273_);
lean_dec(v_p_273_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_Poly_isZero(lean_object* v_p_275_){
_start:
{
if (lean_obj_tag(v_p_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 1;
return v___x_276_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isZero___boxed(lean_object* v_p_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Nat_Internal_Linear_Poly_isZero(v_p_278_);
lean_dec(v_p_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_Poly_isNonZero(lean_object* v_p_281_){
_start:
{
if (lean_obj_tag(v_p_281_) == 0)
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
else
{
lean_object* v_head_283_; lean_object* v_tail_284_; lean_object* v_fst_285_; lean_object* v_snd_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_head_283_ = lean_ctor_get(v_p_281_, 0);
v_tail_284_ = lean_ctor_get(v_p_281_, 1);
v_fst_285_ = lean_ctor_get(v_head_283_, 0);
v_snd_286_ = lean_ctor_get(v_head_283_, 1);
v___x_287_ = lean_unsigned_to_nat(100000000u);
v___x_288_ = lean_nat_dec_eq(v_snd_286_, v___x_287_);
if (v___x_288_ == 0)
{
v_p_281_ = v_tail_284_;
goto _start;
}
else
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_nat_dec_lt(v___x_290_, v_fst_285_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNonZero___boxed(lean_object* v_p_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Nat_Internal_Linear_Poly_isNonZero(v_p_292_);
lean_dec(v_p_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go(lean_object* v_coeff_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
switch(lean_obj_tag(v_a_296_))
{
case 0:
{
lean_object* v_v_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_v_298_ = lean_ctor_get(v_a_296_, 0);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_nat_dec_eq(v_v_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_nat_mul(v_coeff_295_, v_v_298_);
lean_dec(v_coeff_295_);
v___x_302_ = lean_unsigned_to_nat(100000000u);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_297_);
return v___x_304_;
}
else
{
lean_dec(v_coeff_295_);
return v_a_297_;
}
}
case 1:
{
lean_object* v_i_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_i_305_ = lean_ctor_get(v_a_296_, 0);
lean_inc(v_i_305_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_coeff_295_);
lean_ctor_set(v___x_306_, 1, v_i_305_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_a_297_);
return v___x_307_;
}
case 2:
{
lean_object* v_a_308_; lean_object* v_b_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v_a_296_, 0);
v_b_309_ = lean_ctor_get(v_a_296_, 1);
lean_inc(v_coeff_295_);
v___x_310_ = l_Nat_Internal_Linear_Expr_toPoly_go(v_coeff_295_, v_b_309_, v_a_297_);
v_a_296_ = v_a_308_;
v_a_297_ = v___x_310_;
goto _start;
}
case 3:
{
lean_object* v_k_312_; lean_object* v_a_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_k_312_ = lean_ctor_get(v_a_296_, 0);
v_a_313_ = lean_ctor_get(v_a_296_, 1);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_nat_dec_eq(v_k_312_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_nat_mul(v_coeff_295_, v_k_312_);
lean_dec(v_coeff_295_);
v_coeff_295_ = v___x_316_;
v_a_296_ = v_a_313_;
goto _start;
}
else
{
lean_dec(v_coeff_295_);
return v_a_297_;
}
}
default: 
{
lean_object* v_a_318_; lean_object* v_k_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_a_318_ = lean_ctor_get(v_a_296_, 0);
v_k_319_ = lean_ctor_get(v_a_296_, 1);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_nat_dec_eq(v_k_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_nat_mul(v_coeff_295_, v_k_319_);
lean_dec(v_coeff_295_);
v_coeff_295_ = v___x_322_;
v_a_296_ = v_a_318_;
goto _start;
}
else
{
lean_dec(v_coeff_295_);
return v_a_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go___boxed(lean_object* v_coeff_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Nat_Internal_Linear_Expr_toPoly_go(v_coeff_324_, v_a_325_, v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly(lean_object* v_e_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_box(0);
v___x_331_ = l_Nat_Internal_Linear_Expr_toPoly_go(v___x_329_, v_e_328_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly___boxed(lean_object* v_e_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Nat_Internal_Linear_Expr_toPoly(v_e_332_);
lean_dec_ref(v_e_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly(lean_object* v_e_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Nat_Internal_Linear_Expr_toPoly(v_e_334_);
v___x_336_ = l_Nat_Internal_Linear_Poly_norm(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly___boxed(lean_object* v_e_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_e_337_);
lean_dec_ref(v_e_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_inc(lean_object* v_e_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_Nat_Internal_Linear_Expr_inc___closed__0));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v_e_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
if (lean_obj_tag(v_x_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 1;
return v___x_346_;
}
else
{
uint8_t v___x_347_; 
v___x_347_ = 0;
return v___x_347_;
}
}
else
{
if (lean_obj_tag(v_x_345_) == 0)
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
else
{
lean_object* v_head_349_; lean_object* v_head_350_; lean_object* v_tail_351_; lean_object* v_tail_352_; lean_object* v_fst_353_; lean_object* v_snd_354_; lean_object* v_fst_355_; lean_object* v_snd_356_; uint8_t v___x_357_; 
v_head_349_ = lean_ctor_get(v_x_344_, 0);
v_head_350_ = lean_ctor_get(v_x_345_, 0);
v_tail_351_ = lean_ctor_get(v_x_344_, 1);
v_tail_352_ = lean_ctor_get(v_x_345_, 1);
v_fst_353_ = lean_ctor_get(v_head_349_, 0);
v_snd_354_ = lean_ctor_get(v_head_349_, 1);
v_fst_355_ = lean_ctor_get(v_head_350_, 0);
v_snd_356_ = lean_ctor_get(v_head_350_, 1);
v___x_357_ = lean_nat_dec_eq(v_fst_353_, v_fst_355_);
if (v___x_357_ == 0)
{
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_eq(v_snd_354_, v_snd_356_);
if (v___x_358_ == 0)
{
return v___x_358_;
}
else
{
v_x_344_ = v_tail_351_;
v_x_345_ = v_tail_352_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_x_360_, v_x_361_);
lean_dec(v_x_361_);
lean_dec(v_x_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_instBEqPolyCnstr_beq(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint8_t v_eq_366_; lean_object* v_lhs_367_; lean_object* v_rhs_368_; uint8_t v_eq_369_; lean_object* v_lhs_370_; lean_object* v_rhs_371_; 
v_eq_366_ = lean_ctor_get_uint8(v_x_364_, sizeof(void*)*2);
v_lhs_367_ = lean_ctor_get(v_x_364_, 0);
v_rhs_368_ = lean_ctor_get(v_x_364_, 1);
v_eq_369_ = lean_ctor_get_uint8(v_x_365_, sizeof(void*)*2);
v_lhs_370_ = lean_ctor_get(v_x_365_, 0);
v_rhs_371_ = lean_ctor_get(v_x_365_, 1);
if (v_eq_369_ == 0)
{
if (v_eq_366_ == 0)
{
goto v___jp_372_;
}
else
{
return v_eq_369_;
}
}
else
{
if (v_eq_366_ == 0)
{
return v_eq_366_;
}
else
{
goto v___jp_372_;
}
}
v___jp_372_:
{
uint8_t v___x_373_; 
v___x_373_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_lhs_367_, v_lhs_370_);
if (v___x_373_ == 0)
{
return v___x_373_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_rhs_368_, v_rhs_371_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqPolyCnstr_beq___boxed(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Nat_Internal_Linear_instBEqPolyCnstr_beq(v_x_375_, v_x_376_);
lean_dec_ref(v_x_376_);
lean_dec_ref(v_x_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_h__1_383_){
_start:
{
uint8_t v_eq_384_; lean_object* v_lhs_385_; lean_object* v_rhs_386_; uint8_t v_eq_387_; lean_object* v_lhs_388_; lean_object* v_rhs_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_eq_384_ = lean_ctor_get_uint8(v_x_381_, sizeof(void*)*2);
v_lhs_385_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_lhs_385_);
v_rhs_386_ = lean_ctor_get(v_x_381_, 1);
lean_inc(v_rhs_386_);
lean_dec_ref(v_x_381_);
v_eq_387_ = lean_ctor_get_uint8(v_x_382_, sizeof(void*)*2);
v_lhs_388_ = lean_ctor_get(v_x_382_, 0);
lean_inc(v_lhs_388_);
v_rhs_389_ = lean_ctor_get(v_x_382_, 1);
lean_inc(v_rhs_389_);
lean_dec_ref(v_x_382_);
v___x_390_ = lean_box(v_eq_384_);
v___x_391_ = lean_box(v_eq_387_);
v___x_392_ = lean_apply_6(v_h__1_383_, v___x_390_, v_lhs_385_, v_rhs_386_, v___x_391_, v_lhs_388_, v_rhs_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter(lean_object* v_motive_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
uint8_t v_eq_398_; lean_object* v_lhs_399_; lean_object* v_rhs_400_; uint8_t v_eq_401_; lean_object* v_lhs_402_; lean_object* v_rhs_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_eq_398_ = lean_ctor_get_uint8(v_x_394_, sizeof(void*)*2);
v_lhs_399_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_lhs_399_);
v_rhs_400_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_rhs_400_);
lean_dec_ref(v_x_394_);
v_eq_401_ = lean_ctor_get_uint8(v_x_395_, sizeof(void*)*2);
v_lhs_402_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_lhs_402_);
v_rhs_403_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_rhs_403_);
lean_dec_ref(v_x_395_);
v___x_404_ = lean_box(v_eq_398_);
v___x_405_ = lean_box(v_eq_401_);
v___x_406_ = lean_apply_6(v_h__1_396_, v___x_404_, v_lhs_399_, v_rhs_400_, v___x_405_, v_lhs_402_, v_rhs_403_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(lean_object* v_motive_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_h__1_410_, lean_object* v_h__2_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_instBEqPolyCnstr_beq_match__1_splitter(v_motive_407_, v_x_408_, v_x_409_, v_h__1_410_, v_h__2_411_);
lean_dec(v_h__2_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_norm(lean_object* v_c_413_){
_start:
{
uint8_t v_eq_414_; lean_object* v_lhs_415_; lean_object* v_rhs_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_428_; 
v_eq_414_ = lean_ctor_get_uint8(v_c_413_, sizeof(void*)*2);
v_lhs_415_ = lean_ctor_get(v_c_413_, 0);
v_rhs_416_ = lean_ctor_get(v_c_413_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_c_413_);
if (v_isSharedCheck_428_ == 0)
{
v___x_418_ = v_c_413_;
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_rhs_416_);
lean_inc(v_lhs_415_);
lean_dec(v_c_413_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_426_; 
v___x_420_ = l_Nat_Internal_Linear_Poly_norm(v_lhs_415_);
v___x_421_ = l_Nat_Internal_Linear_Poly_norm(v_rhs_416_);
v___x_422_ = l_Nat_Internal_Linear_Poly_cancel(v___x_420_, v___x_421_);
v_fst_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v___x_422_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_snd_424_);
lean_ctor_set(v___x_418_, 0, v_fst_423_);
v___x_426_ = v___x_418_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_423_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_snd_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*2, v_eq_414_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_PolyCnstr_isUnsat(lean_object* v_c_429_){
_start:
{
uint8_t v_eq_430_; lean_object* v_lhs_431_; lean_object* v_rhs_432_; uint8_t v___y_434_; 
v_eq_430_ = lean_ctor_get_uint8(v_c_429_, sizeof(void*)*2);
v_lhs_431_ = lean_ctor_get(v_c_429_, 0);
v_rhs_432_ = lean_ctor_get(v_c_429_, 1);
if (v_eq_430_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Nat_Internal_Linear_Poly_isNonZero(v_lhs_431_);
if (v___x_437_ == 0)
{
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_432_);
return v___x_438_;
}
}
else
{
uint8_t v___x_439_; 
v___x_439_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_431_);
if (v___x_439_ == 0)
{
v___y_434_ = v___x_439_;
goto v___jp_433_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = l_Nat_Internal_Linear_Poly_isNonZero(v_rhs_432_);
v___y_434_ = v___x_440_;
goto v___jp_433_;
}
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = l_Nat_Internal_Linear_Poly_isNonZero(v_lhs_431_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_432_);
return v___x_436_;
}
}
else
{
return v___y_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isUnsat___boxed(lean_object* v_c_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Nat_Internal_Linear_PolyCnstr_isUnsat(v_c_441_);
lean_dec_ref(v_c_441_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_PolyCnstr_isValid(lean_object* v_c_444_){
_start:
{
uint8_t v_eq_445_; 
v_eq_445_ = lean_ctor_get_uint8(v_c_444_, sizeof(void*)*2);
if (v_eq_445_ == 0)
{
lean_object* v_lhs_446_; uint8_t v___x_447_; 
v_lhs_446_ = lean_ctor_get(v_c_444_, 0);
v___x_447_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_446_);
return v___x_447_;
}
else
{
lean_object* v_lhs_448_; lean_object* v_rhs_449_; uint8_t v___x_450_; 
v_lhs_448_ = lean_ctor_get(v_c_444_, 0);
v_rhs_449_ = lean_ctor_get(v_c_444_, 1);
v___x_450_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_448_);
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_449_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isValid___boxed(lean_object* v_c_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Nat_Internal_Linear_PolyCnstr_isValid(v_c_452_);
lean_dec_ref(v_c_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toPoly(lean_object* v_c_455_){
_start:
{
uint8_t v_eq_456_; lean_object* v_lhs_457_; lean_object* v_rhs_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v_eq_456_ = lean_ctor_get_uint8(v_c_455_, sizeof(void*)*2);
v_lhs_457_ = lean_ctor_get(v_c_455_, 0);
v_rhs_458_ = lean_ctor_get(v_c_455_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_c_455_);
if (v_isSharedCheck_467_ == 0)
{
v___x_460_ = v_c_455_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_rhs_458_);
lean_inc(v_lhs_457_);
lean_dec(v_c_455_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = l_Nat_Internal_Linear_Expr_toPoly(v_lhs_457_);
lean_dec_ref(v_lhs_457_);
v___x_463_ = l_Nat_Internal_Linear_Expr_toPoly(v_rhs_458_);
lean_dec_ref(v_rhs_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_463_);
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
lean_ctor_set_uint8(v_reuseFailAlloc_466_, sizeof(void*)*2, v_eq_456_);
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
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toNormPoly(lean_object* v_c_468_){
_start:
{
uint8_t v_eq_469_; lean_object* v_lhs_470_; lean_object* v_rhs_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_483_; 
v_eq_469_ = lean_ctor_get_uint8(v_c_468_, sizeof(void*)*2);
v_lhs_470_ = lean_ctor_get(v_c_468_, 0);
v_rhs_471_ = lean_ctor_get(v_c_468_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_c_468_);
if (v_isSharedCheck_483_ == 0)
{
v___x_473_ = v_c_468_;
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_rhs_471_);
lean_inc(v_lhs_470_);
lean_dec(v_c_468_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v___x_481_; 
v___x_475_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_lhs_470_);
lean_dec_ref(v_lhs_470_);
v___x_476_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_rhs_471_);
lean_dec_ref(v_rhs_471_);
v___x_477_ = l_Nat_Internal_Linear_Poly_cancel(v___x_475_, v___x_476_);
v_fst_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_fst_478_);
v_snd_479_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_snd_479_);
lean_dec_ref(v___x_477_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_snd_479_);
lean_ctor_set(v___x_473_, 0, v_fst_478_);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fst_478_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_snd_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*2, v_eq_469_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_monomialToExpr(lean_object* v_k_484_, lean_object* v_v_485_){
_start:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(100000000u);
v___x_487_ = lean_nat_dec_eq(v_v_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_dec_eq(v_k_484_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_v_485_);
v___x_491_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_491_, 0, v_k_484_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_k_484_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_v_485_);
return v___x_492_;
}
}
else
{
lean_object* v___x_493_; 
lean_dec(v_v_485_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_k_484_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr_go(lean_object* v_e_494_, lean_object* v_p_495_){
_start:
{
if (lean_obj_tag(v_p_495_) == 0)
{
return v_e_494_;
}
else
{
lean_object* v_head_496_; lean_object* v_tail_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_508_; 
v_head_496_ = lean_ctor_get(v_p_495_, 0);
lean_inc(v_head_496_);
v_tail_497_ = lean_ctor_get(v_p_495_, 1);
lean_inc(v_tail_497_);
lean_dec_ref_known(v_p_495_, 2);
v_fst_498_ = lean_ctor_get(v_head_496_, 0);
v_snd_499_ = lean_ctor_get(v_head_496_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_head_496_);
if (v_isSharedCheck_508_ == 0)
{
v___x_501_ = v_head_496_;
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snd_499_);
lean_inc(v_fst_498_);
lean_dec(v_head_496_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Nat_Internal_Linear_monomialToExpr(v_fst_498_, v_snd_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 2);
lean_ctor_set(v___x_501_, 1, v___x_503_);
lean_ctor_set(v___x_501_, 0, v_e_494_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_e_494_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v_e_494_ = v___x_505_;
v_p_495_ = v_tail_497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr(lean_object* v_p_509_){
_start:
{
if (lean_obj_tag(v_p_509_) == 0)
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0));
return v___x_510_;
}
else
{
lean_object* v_head_511_; lean_object* v_tail_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_head_511_ = lean_ctor_get(v_p_509_, 0);
lean_inc(v_head_511_);
v_tail_512_ = lean_ctor_get(v_p_509_, 1);
lean_inc(v_tail_512_);
lean_dec_ref_known(v_p_509_, 2);
v_fst_513_ = lean_ctor_get(v_head_511_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_head_511_, 1);
lean_inc(v_snd_514_);
lean_dec(v_head_511_);
v___x_515_ = l_Nat_Internal_Linear_monomialToExpr(v_fst_513_, v_snd_514_);
v___x_516_ = l_Nat_Internal_Linear_Poly_toExpr_go(v___x_515_, v_tail_512_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_toExpr(lean_object* v_c_517_){
_start:
{
uint8_t v_eq_518_; lean_object* v_lhs_519_; lean_object* v_rhs_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_529_; 
v_eq_518_ = lean_ctor_get_uint8(v_c_517_, sizeof(void*)*2);
v_lhs_519_ = lean_ctor_get(v_c_517_, 0);
v_rhs_520_ = lean_ctor_get(v_c_517_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_c_517_);
if (v_isSharedCheck_529_ == 0)
{
v___x_522_ = v_c_517_;
v_isShared_523_ = v_isSharedCheck_529_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_rhs_520_);
lean_inc(v_lhs_519_);
lean_dec(v_c_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_529_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = l_Nat_Internal_Linear_Poly_toExpr(v_lhs_519_);
v___x_525_ = l_Nat_Internal_Linear_Poly_toExpr(v_rhs_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_525_);
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*2, v_eq_518_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_denote_match__1_splitter___redArg(lean_object* v_p_530_, lean_object* v_h__1_531_, lean_object* v_h__2_532_){
_start:
{
if (lean_obj_tag(v_p_530_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_h__2_532_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_apply_1(v_h__1_531_, v___x_533_);
return v___x_534_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_539_; 
lean_dec(v_h__1_531_);
v_head_535_ = lean_ctor_get(v_p_530_, 0);
lean_inc(v_head_535_);
v_tail_536_ = lean_ctor_get(v_p_530_, 1);
lean_inc(v_tail_536_);
lean_dec_ref_known(v_p_530_, 2);
v_fst_537_ = lean_ctor_get(v_head_535_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v_head_535_, 1);
lean_inc(v_snd_538_);
lean_dec(v_head_535_);
v___x_539_ = lean_apply_3(v_h__2_532_, v_fst_537_, v_snd_538_, v_tail_536_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_denote_match__1_splitter(lean_object* v_motive_540_, lean_object* v_p_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
if (lean_obj_tag(v_p_541_) == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__2_543_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__1_542_, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v_head_546_; lean_object* v_tail_547_; lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_550_; 
lean_dec(v_h__1_542_);
v_head_546_ = lean_ctor_get(v_p_541_, 0);
lean_inc(v_head_546_);
v_tail_547_ = lean_ctor_get(v_p_541_, 1);
lean_inc(v_tail_547_);
lean_dec_ref_known(v_p_541_, 2);
v_fst_548_ = lean_ctor_get(v_head_546_, 0);
lean_inc(v_fst_548_);
v_snd_549_ = lean_ctor_get(v_head_546_, 1);
lean_inc(v_snd_549_);
lean_dec(v_head_546_);
v___x_550_ = lean_apply_3(v_h__2_543_, v_fst_548_, v_snd_549_, v_tail_547_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object* v_fuel_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_){
_start:
{
lean_object* v_zero_554_; uint8_t v_isZero_555_; 
v_zero_554_ = lean_unsigned_to_nat(0u);
v_isZero_555_ = lean_nat_dec_eq(v_fuel_551_, v_zero_554_);
if (v_isZero_555_ == 1)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v_h__2_553_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_apply_1(v_h__1_552_, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v_one_558_; lean_object* v_n_559_; lean_object* v___x_560_; 
lean_dec(v_h__1_552_);
v_one_558_ = lean_unsigned_to_nat(1u);
v_n_559_ = lean_nat_sub(v_fuel_551_, v_one_558_);
v___x_560_ = lean_apply_1(v_h__2_553_, v_n_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object* v_fuel_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(v_fuel_561_, v_h__1_562_, v_h__2_563_);
lean_dec(v_fuel_561_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(lean_object* v_motive_565_, lean_object* v_fuel_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
lean_object* v_zero_569_; uint8_t v_isZero_570_; 
v_zero_569_ = lean_unsigned_to_nat(0u);
v_isZero_570_ = lean_nat_dec_eq(v_fuel_566_, v_zero_569_);
if (v_isZero_570_ == 1)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_h__2_568_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_apply_1(v_h__1_567_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_one_573_; lean_object* v_n_574_; lean_object* v___x_575_; 
lean_dec(v_h__1_567_);
v_one_573_ = lean_unsigned_to_nat(1u);
v_n_574_ = lean_nat_sub(v_fuel_566_, v_one_573_);
v___x_575_ = lean_apply_1(v_h__2_568_, v_n_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object* v_motive_576_, lean_object* v_fuel_577_, lean_object* v_h__1_578_, lean_object* v_h__2_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(v_motive_576_, v_fuel_577_, v_h__1_578_, v_h__2_579_);
lean_dec(v_fuel_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object* v_m_u2081_581_, lean_object* v_m_u2082_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_, lean_object* v_h__3_585_){
_start:
{
if (lean_obj_tag(v_m_u2082_582_) == 0)
{
lean_object* v___x_586_; 
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
v___x_586_ = lean_apply_1(v_h__1_583_, v_m_u2081_581_);
return v___x_586_;
}
else
{
lean_dec(v_h__1_583_);
if (lean_obj_tag(v_m_u2081_581_) == 0)
{
lean_object* v___x_587_; 
lean_dec(v_h__3_585_);
v___x_587_ = lean_apply_2(v_h__2_584_, v_m_u2082_582_, lean_box(0));
return v___x_587_;
}
else
{
lean_object* v_head_588_; lean_object* v_head_589_; lean_object* v_tail_590_; lean_object* v_tail_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; 
lean_dec(v_h__2_584_);
v_head_588_ = lean_ctor_get(v_m_u2081_581_, 0);
lean_inc(v_head_588_);
v_head_589_ = lean_ctor_get(v_m_u2082_582_, 0);
lean_inc(v_head_589_);
v_tail_590_ = lean_ctor_get(v_m_u2082_582_, 1);
lean_inc(v_tail_590_);
lean_dec_ref_known(v_m_u2082_582_, 2);
v_tail_591_ = lean_ctor_get(v_m_u2081_581_, 1);
lean_inc(v_tail_591_);
lean_dec_ref_known(v_m_u2081_581_, 2);
v_fst_592_ = lean_ctor_get(v_head_588_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v_head_588_, 1);
lean_inc(v_snd_593_);
lean_dec(v_head_588_);
v_fst_594_ = lean_ctor_get(v_head_589_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v_head_589_, 1);
lean_inc(v_snd_595_);
lean_dec(v_head_589_);
v___x_596_ = lean_apply_6(v_h__3_585_, v_fst_592_, v_snd_593_, v_tail_591_, v_fst_594_, v_snd_595_, v_tail_590_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter(lean_object* v_motive_597_, lean_object* v_m_u2081_598_, lean_object* v_m_u2082_599_, lean_object* v_h__1_600_, lean_object* v_h__2_601_, lean_object* v_h__3_602_){
_start:
{
if (lean_obj_tag(v_m_u2082_599_) == 0)
{
lean_object* v___x_603_; 
lean_dec(v_h__3_602_);
lean_dec(v_h__2_601_);
v___x_603_ = lean_apply_1(v_h__1_600_, v_m_u2081_598_);
return v___x_603_;
}
else
{
lean_dec(v_h__1_600_);
if (lean_obj_tag(v_m_u2081_598_) == 0)
{
lean_object* v___x_604_; 
lean_dec(v_h__3_602_);
v___x_604_ = lean_apply_2(v_h__2_601_, v_m_u2082_599_, lean_box(0));
return v___x_604_;
}
else
{
lean_object* v_head_605_; lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v_tail_608_; lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v_fst_611_; lean_object* v_snd_612_; lean_object* v___x_613_; 
lean_dec(v_h__2_601_);
v_head_605_ = lean_ctor_get(v_m_u2081_598_, 0);
lean_inc(v_head_605_);
v_head_606_ = lean_ctor_get(v_m_u2082_599_, 0);
lean_inc(v_head_606_);
v_tail_607_ = lean_ctor_get(v_m_u2082_599_, 1);
lean_inc(v_tail_607_);
lean_dec_ref_known(v_m_u2082_599_, 2);
v_tail_608_ = lean_ctor_get(v_m_u2081_598_, 1);
lean_inc(v_tail_608_);
lean_dec_ref_known(v_m_u2081_598_, 2);
v_fst_609_ = lean_ctor_get(v_head_605_, 0);
lean_inc(v_fst_609_);
v_snd_610_ = lean_ctor_get(v_head_605_, 1);
lean_inc(v_snd_610_);
lean_dec(v_head_605_);
v_fst_611_ = lean_ctor_get(v_head_606_, 0);
lean_inc(v_fst_611_);
v_snd_612_ = lean_ctor_get(v_head_606_, 1);
lean_inc(v_snd_612_);
lean_dec(v_head_606_);
v___x_613_ = lean_apply_6(v_h__3_602_, v_fst_609_, v_snd_610_, v_tail_608_, v_fst_611_, v_snd_612_, v_tail_607_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_, lean_object* v_h__3_617_, lean_object* v_h__4_618_, lean_object* v_h__5_619_){
_start:
{
switch(lean_obj_tag(v_x_614_))
{
case 0:
{
lean_object* v_v_620_; lean_object* v___x_621_; 
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
v_v_620_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_v_620_);
lean_dec_ref_known(v_x_614_, 1);
v___x_621_ = lean_apply_1(v_h__1_615_, v_v_620_);
return v___x_621_;
}
case 1:
{
lean_object* v_i_622_; lean_object* v___x_623_; 
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__1_615_);
v_i_622_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_i_622_);
lean_dec_ref_known(v_x_614_, 1);
v___x_623_ = lean_apply_1(v_h__2_616_, v_i_622_);
return v___x_623_;
}
case 2:
{
lean_object* v_a_624_; lean_object* v_b_625_; lean_object* v___x_626_; 
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_a_624_ = lean_ctor_get(v_x_614_, 0);
lean_inc_ref(v_a_624_);
v_b_625_ = lean_ctor_get(v_x_614_, 1);
lean_inc_ref(v_b_625_);
lean_dec_ref_known(v_x_614_, 2);
v___x_626_ = lean_apply_2(v_h__3_617_, v_a_624_, v_b_625_);
return v___x_626_;
}
case 3:
{
lean_object* v_k_627_; lean_object* v_a_628_; lean_object* v___x_629_; 
lean_dec(v_h__5_619_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_k_627_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_k_627_);
v_a_628_ = lean_ctor_get(v_x_614_, 1);
lean_inc_ref(v_a_628_);
lean_dec_ref_known(v_x_614_, 2);
v___x_629_ = lean_apply_2(v_h__4_618_, v_k_627_, v_a_628_);
return v___x_629_;
}
default: 
{
lean_object* v_a_630_; lean_object* v_k_631_; lean_object* v___x_632_; 
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_a_630_ = lean_ctor_get(v_x_614_, 0);
lean_inc_ref(v_a_630_);
v_k_631_ = lean_ctor_get(v_x_614_, 1);
lean_inc(v_k_631_);
lean_dec_ref_known(v_x_614_, 2);
v___x_632_ = lean_apply_2(v_h__5_619_, v_a_630_, v_k_631_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter(lean_object* v_motive_633_, lean_object* v_x_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_, lean_object* v_h__3_637_, lean_object* v_h__4_638_, lean_object* v_h__5_639_){
_start:
{
switch(lean_obj_tag(v_x_634_))
{
case 0:
{
lean_object* v_v_640_; lean_object* v___x_641_; 
lean_dec(v_h__5_639_);
lean_dec(v_h__4_638_);
lean_dec(v_h__3_637_);
lean_dec(v_h__2_636_);
v_v_640_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_v_640_);
lean_dec_ref_known(v_x_634_, 1);
v___x_641_ = lean_apply_1(v_h__1_635_, v_v_640_);
return v___x_641_;
}
case 1:
{
lean_object* v_i_642_; lean_object* v___x_643_; 
lean_dec(v_h__5_639_);
lean_dec(v_h__4_638_);
lean_dec(v_h__3_637_);
lean_dec(v_h__1_635_);
v_i_642_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_i_642_);
lean_dec_ref_known(v_x_634_, 1);
v___x_643_ = lean_apply_1(v_h__2_636_, v_i_642_);
return v___x_643_;
}
case 2:
{
lean_object* v_a_644_; lean_object* v_b_645_; lean_object* v___x_646_; 
lean_dec(v_h__5_639_);
lean_dec(v_h__4_638_);
lean_dec(v_h__2_636_);
lean_dec(v_h__1_635_);
v_a_644_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_a_644_);
v_b_645_ = lean_ctor_get(v_x_634_, 1);
lean_inc_ref(v_b_645_);
lean_dec_ref_known(v_x_634_, 2);
v___x_646_ = lean_apply_2(v_h__3_637_, v_a_644_, v_b_645_);
return v___x_646_;
}
case 3:
{
lean_object* v_k_647_; lean_object* v_a_648_; lean_object* v___x_649_; 
lean_dec(v_h__5_639_);
lean_dec(v_h__3_637_);
lean_dec(v_h__2_636_);
lean_dec(v_h__1_635_);
v_k_647_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_k_647_);
v_a_648_ = lean_ctor_get(v_x_634_, 1);
lean_inc_ref(v_a_648_);
lean_dec_ref_known(v_x_634_, 2);
v___x_649_ = lean_apply_2(v_h__4_638_, v_k_647_, v_a_648_);
return v___x_649_;
}
default: 
{
lean_object* v_a_650_; lean_object* v_k_651_; lean_object* v___x_652_; 
lean_dec(v_h__4_638_);
lean_dec(v_h__3_637_);
lean_dec(v_h__2_636_);
lean_dec(v_h__1_635_);
v_a_650_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_a_650_);
v_k_651_ = lean_ctor_get(v_x_634_, 1);
lean_inc(v_k_651_);
lean_dec_ref_known(v_x_634_, 2);
v___x_652_ = lean_apply_2(v_h__5_639_, v_a_650_, v_k_651_);
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter___redArg(lean_object* v_p_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
if (lean_obj_tag(v_p_653_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_h__2_655_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_apply_1(v_h__1_654_, v___x_656_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
lean_dec(v_h__1_654_);
v___x_658_ = lean_apply_2(v_h__2_655_, v_p_653_, lean_box(0));
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter(lean_object* v_motive_659_, lean_object* v_p_660_, lean_object* v_h__1_661_, lean_object* v_h__2_662_){
_start:
{
if (lean_obj_tag(v_p_660_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v_h__2_662_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_apply_1(v_h__1_661_, v___x_663_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
lean_dec(v_h__1_661_);
v___x_665_ = lean_apply_2(v_h__2_662_, v_p_660_, lean_box(0));
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___redArg(lean_object* v_h_u2082_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = lean_apply_1(v_h_u2082_666_, lean_box(0));
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset(lean_object* v_00_u03b1_668_, lean_object* v_a_669_, lean_object* v_b_670_, lean_object* v_k_671_, lean_object* v_h_u2081_672_, lean_object* v_h_u2082_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_apply_1(v_h_u2082_673_, lean_box(0));
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___boxed(lean_object* v_00_u03b1_675_, lean_object* v_a_676_, lean_object* v_b_677_, lean_object* v_k_678_, lean_object* v_h_u2081_679_, lean_object* v_h_u2082_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Nat_Internal_elimOffset(v_00_u03b1_675_, v_a_676_, v_b_677_, v_k_678_, v_h_u2081_679_, v_h_u2082_680_);
lean_dec(v_k_678_);
lean_dec(v_b_677_);
lean_dec(v_a_676_);
return v_res_681_;
}
}
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_Internal_Linear_fixedVar = _init_l_Nat_Internal_Linear_fixedVar();
lean_mark_persistent(l_Nat_Internal_Linear_fixedVar);
l_Nat_Internal_Linear_hugeFuel = _init_l_Nat_Internal_Linear_hugeFuel();
lean_mark_persistent(l_Nat_Internal_Linear_hugeFuel);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Internal_Linear(builtin);
}
#ifdef __cplusplus
}
#endif
