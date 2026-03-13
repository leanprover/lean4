// Lean compiler output
// Module: Init.Data.Nat.Linear
// Imports: public import Init.Data.RArray import Init.LawfulBEqTactics import Init.ByCases import Init.Data.Prod
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_fixedVar;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_Linear_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_Linear_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Nat_Linear_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Linear_instInhabitedExpr_default = (const lean_object*)&l_Nat_Linear_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Linear_instInhabitedExpr = (const lean_object*)&l_Nat_Linear_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_Linear_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_Linear_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_Linear_instBEqExpr___closed__0 = (const lean_object*)&l_Nat_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Linear_instBEqExpr = (const lean_object*)&l_Nat_Linear_instBEqExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_hugeFuel;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancel(lean_object*, lean_object*);
static const lean_ctor_object l_Nat_Linear_Poly_isNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_Linear_Poly_isNum_x3f___closed__0 = (const lean_object*)&l_Nat_Linear_Poly_isNum_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isNonZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNonZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly___boxed(lean_object*);
static const lean_ctor_object l_Nat_Linear_Expr_inc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Nat_Linear_Expr_inc___closed__0 = (const lean_object*)&l_Nat_Linear_Expr_inc___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_inc(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqPolyCnstr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqPolyCnstr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_Linear_instBEqPolyCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_Linear_instBEqPolyCnstr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_Linear_instBEqPolyCnstr___closed__0 = (const lean_object*)&l_Nat_Linear_instBEqPolyCnstr___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Linear_instBEqPolyCnstr = (const lean_object*)&l_Nat_Linear_instBEqPolyCnstr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isValid___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_monomialToExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_Linear_fixedVar(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(100000000u);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx(lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Nat_Linear_Expr_ctorIdx(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
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
lean_dec_ref(v_t_10_);
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
lean_dec_ref(v_t_10_);
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
lean_dec_ref(v_t_10_);
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
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_25_, v_k_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___boxed(lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Nat_Linear_Expr_ctorElim(v_motive_29_, v_ctorIdx_30_, v_t_31_, v_h_32_, v_k_33_);
lean_dec(v_ctorIdx_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim___redArg(lean_object* v_t_35_, lean_object* v_num_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_35_, v_num_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_num_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_39_, v_num_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim___redArg(lean_object* v_t_43_, lean_object* v_var_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_43_, v_var_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_var_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_47_, v_var_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim___redArg(lean_object* v_t_51_, lean_object* v_add_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_51_, v_add_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_add_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_55_, v_add_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim___redArg(lean_object* v_t_59_, lean_object* v_mulL_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_59_, v_mulL_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_mulL_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_63_, v_mulL_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim___redArg(lean_object* v_t_67_, lean_object* v_mulR_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_67_, v_mulR_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_mulR_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_71_, v_mulR_73_);
return v___x_74_;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqExpr_beq(lean_object* v_x_79_, lean_object* v_x_80_){
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
v___x_93_ = l_Nat_Linear_instBEqExpr_beq(v_a_89_, v_a_91_);
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
v___x_107_ = l_Nat_Linear_instBEqExpr_beq(v_a_103_, v_a_105_);
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
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqExpr_beq___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Nat_Linear_instBEqExpr_beq(v_x_110_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec_ref(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_insert(lean_object* v_k_116_, lean_object* v_v_117_, lean_object* v_p_118_){
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
v___x_130_ = l_Nat_Linear_Poly_insert(v_k_116_, v_v_117_, v_tail_122_);
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
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm_go(lean_object* v_p_160_, lean_object* v_r_161_){
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
lean_dec_ref(v_p_160_);
v_fst_164_ = lean_ctor_get(v_head_162_, 0);
lean_inc(v_fst_164_);
v_snd_165_ = lean_ctor_get(v_head_162_, 1);
lean_inc(v_snd_165_);
lean_dec(v_head_162_);
v___x_166_ = l_Nat_Linear_Poly_insert(v_fst_164_, v_snd_165_, v_r_161_);
v_p_160_ = v_tail_163_;
v_r_161_ = v___x_166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm(lean_object* v_p_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_box(0);
v___x_170_ = l_Nat_Linear_Poly_norm_go(v_p_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancelAux(lean_object* v_fuel_171_, lean_object* v_m_u2081_172_, lean_object* v_m_u2082_173_, lean_object* v_r_u2081_174_, lean_object* v_r_u2082_175_){
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
static lean_object* _init_l_Nat_Linear_hugeFuel(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_unsigned_to_nat(1000000u);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancel(lean_object* v_p_u2081_255_, lean_object* v_p_u2082_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(1000000u);
v___x_258_ = lean_box(0);
v___x_259_ = l_Nat_Linear_Poly_cancelAux(v___x_257_, v_p_u2081_255_, v_p_u2082_256_, v___x_258_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f(lean_object* v_p_262_){
_start:
{
if (lean_obj_tag(v_p_262_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l_Nat_Linear_Poly_isNum_x3f___closed__0));
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
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f___boxed(lean_object* v_p_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Nat_Linear_Poly_isNum_x3f(v_p_273_);
lean_dec(v_p_273_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isZero(lean_object* v_p_275_){
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
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isZero___boxed(lean_object* v_p_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Nat_Linear_Poly_isZero(v_p_278_);
lean_dec(v_p_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isNonZero(lean_object* v_p_281_){
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
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNonZero___boxed(lean_object* v_p_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Nat_Linear_Poly_isNonZero(v_p_292_);
lean_dec(v_p_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go(lean_object* v_coeff_295_, lean_object* v_a_296_, lean_object* v_a_297_){
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
v___x_310_ = l_Nat_Linear_Expr_toPoly_go(v_coeff_295_, v_b_309_, v_a_297_);
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
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go___boxed(lean_object* v_coeff_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Nat_Linear_Expr_toPoly_go(v_coeff_324_, v_a_325_, v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly(lean_object* v_e_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_box(0);
v___x_331_ = l_Nat_Linear_Expr_toPoly_go(v___x_329_, v_e_328_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly___boxed(lean_object* v_e_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Nat_Linear_Expr_toPoly(v_e_332_);
lean_dec_ref(v_e_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly(lean_object* v_e_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Nat_Linear_Expr_toPoly(v_e_334_);
v___x_336_ = l_Nat_Linear_Poly_norm(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly___boxed(lean_object* v_e_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Nat_Linear_Expr_toNormPoly(v_e_337_);
lean_dec_ref(v_e_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_inc(lean_object* v_e_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_Nat_Linear_Expr_inc___closed__0));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v_e_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(lean_object* v_x_344_, lean_object* v_x_345_){
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
lean_object* v_head_349_; lean_object* v_tail_350_; lean_object* v_head_351_; lean_object* v_tail_352_; uint8_t v___y_354_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v_fst_358_; lean_object* v_snd_359_; uint8_t v___x_360_; 
v_head_349_ = lean_ctor_get(v_x_344_, 0);
v_tail_350_ = lean_ctor_get(v_x_344_, 1);
v_head_351_ = lean_ctor_get(v_x_345_, 0);
v_tail_352_ = lean_ctor_get(v_x_345_, 1);
v_fst_356_ = lean_ctor_get(v_head_349_, 0);
v_snd_357_ = lean_ctor_get(v_head_349_, 1);
v_fst_358_ = lean_ctor_get(v_head_351_, 0);
v_snd_359_ = lean_ctor_get(v_head_351_, 1);
v___x_360_ = lean_nat_dec_eq(v_fst_356_, v_fst_358_);
if (v___x_360_ == 0)
{
v___y_354_ = v___x_360_;
goto v___jp_353_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_eq(v_snd_357_, v_snd_359_);
v___y_354_ = v___x_361_;
goto v___jp_353_;
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
return v___y_354_;
}
else
{
v_x_344_ = v_tail_350_;
v_x_345_ = v_tail_352_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(v_x_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec(v_x_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqPolyCnstr_beq(lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_eq_368_; lean_object* v_lhs_369_; lean_object* v_rhs_370_; uint8_t v_eq_371_; lean_object* v_lhs_372_; lean_object* v_rhs_373_; 
v_eq_368_ = lean_ctor_get_uint8(v_x_366_, sizeof(void*)*2);
v_lhs_369_ = lean_ctor_get(v_x_366_, 0);
v_rhs_370_ = lean_ctor_get(v_x_366_, 1);
v_eq_371_ = lean_ctor_get_uint8(v_x_367_, sizeof(void*)*2);
v_lhs_372_ = lean_ctor_get(v_x_367_, 0);
v_rhs_373_ = lean_ctor_get(v_x_367_, 1);
if (v_eq_368_ == 0)
{
if (v_eq_371_ == 0)
{
goto v___jp_374_;
}
else
{
return v_eq_368_;
}
}
else
{
if (v_eq_371_ == 0)
{
return v_eq_371_;
}
else
{
goto v___jp_374_;
}
}
v___jp_374_:
{
uint8_t v___x_375_; 
v___x_375_ = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(v_lhs_369_, v_lhs_372_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
uint8_t v___x_376_; 
v___x_376_ = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(v_rhs_370_, v_rhs_373_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqPolyCnstr_beq___boxed(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Nat_Linear_instBEqPolyCnstr_beq(v_x_377_, v_x_378_);
lean_dec_ref(v_x_378_);
lean_dec_ref(v_x_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_h__1_385_){
_start:
{
uint8_t v_eq_386_; lean_object* v_lhs_387_; lean_object* v_rhs_388_; uint8_t v_eq_389_; lean_object* v_lhs_390_; lean_object* v_rhs_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_eq_386_ = lean_ctor_get_uint8(v_x_383_, sizeof(void*)*2);
v_lhs_387_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_lhs_387_);
v_rhs_388_ = lean_ctor_get(v_x_383_, 1);
lean_inc(v_rhs_388_);
lean_dec_ref(v_x_383_);
v_eq_389_ = lean_ctor_get_uint8(v_x_384_, sizeof(void*)*2);
v_lhs_390_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_lhs_390_);
v_rhs_391_ = lean_ctor_get(v_x_384_, 1);
lean_inc(v_rhs_391_);
lean_dec_ref(v_x_384_);
v___x_392_ = lean_box(v_eq_386_);
v___x_393_ = lean_box(v_eq_389_);
v___x_394_ = lean_apply_6(v_h__1_385_, v___x_392_, v_lhs_387_, v_rhs_388_, v___x_393_, v_lhs_390_, v_rhs_391_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(lean_object* v_motive_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_){
_start:
{
uint8_t v_eq_400_; lean_object* v_lhs_401_; lean_object* v_rhs_402_; uint8_t v_eq_403_; lean_object* v_lhs_404_; lean_object* v_rhs_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_eq_400_ = lean_ctor_get_uint8(v_x_396_, sizeof(void*)*2);
v_lhs_401_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_lhs_401_);
v_rhs_402_ = lean_ctor_get(v_x_396_, 1);
lean_inc(v_rhs_402_);
lean_dec_ref(v_x_396_);
v_eq_403_ = lean_ctor_get_uint8(v_x_397_, sizeof(void*)*2);
v_lhs_404_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_lhs_404_);
v_rhs_405_ = lean_ctor_get(v_x_397_, 1);
lean_inc(v_rhs_405_);
lean_dec_ref(v_x_397_);
v___x_406_ = lean_box(v_eq_400_);
v___x_407_ = lean_box(v_eq_403_);
v___x_408_ = lean_apply_6(v_h__1_398_, v___x_406_, v_lhs_401_, v_rhs_402_, v___x_407_, v_lhs_404_, v_rhs_405_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(v_motive_409_, v_x_410_, v_x_411_, v_h__1_412_, v_h__2_413_);
lean_dec(v_h__2_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object* v_c_415_){
_start:
{
uint8_t v_eq_416_; lean_object* v_lhs_417_; lean_object* v_rhs_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_430_; 
v_eq_416_ = lean_ctor_get_uint8(v_c_415_, sizeof(void*)*2);
v_lhs_417_ = lean_ctor_get(v_c_415_, 0);
v_rhs_418_ = lean_ctor_get(v_c_415_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_c_415_);
if (v_isSharedCheck_430_ == 0)
{
v___x_420_ = v_c_415_;
v_isShared_421_ = v_isSharedCheck_430_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_rhs_418_);
lean_inc(v_lhs_417_);
lean_dec(v_c_415_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_430_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_428_; 
v___x_422_ = l_Nat_Linear_Poly_norm(v_lhs_417_);
v___x_423_ = l_Nat_Linear_Poly_norm(v_rhs_418_);
v___x_424_ = l_Nat_Linear_Poly_cancel(v___x_422_, v___x_423_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_fst_425_);
v_snd_426_ = lean_ctor_get(v___x_424_, 1);
lean_inc(v_snd_426_);
lean_dec_ref(v___x_424_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v_snd_426_);
lean_ctor_set(v___x_420_, 0, v_fst_425_);
v___x_428_ = v___x_420_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fst_425_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_snd_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*2, v_eq_416_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object* v_c_431_){
_start:
{
uint8_t v_eq_432_; lean_object* v_lhs_433_; lean_object* v_rhs_434_; uint8_t v___y_436_; 
v_eq_432_ = lean_ctor_get_uint8(v_c_431_, sizeof(void*)*2);
v_lhs_433_ = lean_ctor_get(v_c_431_, 0);
v_rhs_434_ = lean_ctor_get(v_c_431_, 1);
if (v_eq_432_ == 0)
{
uint8_t v___x_439_; 
v___x_439_ = l_Nat_Linear_Poly_isNonZero(v_lhs_433_);
if (v___x_439_ == 0)
{
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = l_Nat_Linear_Poly_isZero(v_rhs_434_);
return v___x_440_;
}
}
else
{
uint8_t v___x_441_; 
v___x_441_ = l_Nat_Linear_Poly_isZero(v_lhs_433_);
if (v___x_441_ == 0)
{
v___y_436_ = v___x_441_;
goto v___jp_435_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = l_Nat_Linear_Poly_isNonZero(v_rhs_434_);
v___y_436_ = v___x_442_;
goto v___jp_435_;
}
}
v___jp_435_:
{
if (v___y_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Nat_Linear_Poly_isNonZero(v_lhs_433_);
if (v___x_437_ == 0)
{
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = l_Nat_Linear_Poly_isZero(v_rhs_434_);
return v___x_438_;
}
}
else
{
return v___y_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isUnsat___boxed(lean_object* v_c_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Nat_Linear_PolyCnstr_isUnsat(v_c_443_);
lean_dec_ref(v_c_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object* v_c_446_){
_start:
{
uint8_t v_eq_447_; 
v_eq_447_ = lean_ctor_get_uint8(v_c_446_, sizeof(void*)*2);
if (v_eq_447_ == 0)
{
lean_object* v_lhs_448_; uint8_t v___x_449_; 
v_lhs_448_ = lean_ctor_get(v_c_446_, 0);
v___x_449_ = l_Nat_Linear_Poly_isZero(v_lhs_448_);
return v___x_449_;
}
else
{
lean_object* v_lhs_450_; lean_object* v_rhs_451_; uint8_t v___x_452_; 
v_lhs_450_ = lean_ctor_get(v_c_446_, 0);
v_rhs_451_ = lean_ctor_get(v_c_446_, 1);
v___x_452_ = l_Nat_Linear_Poly_isZero(v_lhs_450_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = l_Nat_Linear_Poly_isZero(v_rhs_451_);
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isValid___boxed(lean_object* v_c_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Nat_Linear_PolyCnstr_isValid(v_c_454_);
lean_dec_ref(v_c_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object* v_c_457_){
_start:
{
uint8_t v_eq_458_; lean_object* v_lhs_459_; lean_object* v_rhs_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_eq_458_ = lean_ctor_get_uint8(v_c_457_, sizeof(void*)*2);
v_lhs_459_ = lean_ctor_get(v_c_457_, 0);
v_rhs_460_ = lean_ctor_get(v_c_457_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_c_457_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v_c_457_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_rhs_460_);
lean_inc(v_lhs_459_);
lean_dec(v_c_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = l_Nat_Linear_Expr_toPoly(v_lhs_459_);
lean_dec_ref(v_lhs_459_);
v___x_465_ = l_Nat_Linear_Expr_toPoly(v_rhs_460_);
lean_dec_ref(v_rhs_460_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_465_);
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*2, v_eq_458_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toNormPoly(lean_object* v_c_470_){
_start:
{
uint8_t v_eq_471_; lean_object* v_lhs_472_; lean_object* v_rhs_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_eq_471_ = lean_ctor_get_uint8(v_c_470_, sizeof(void*)*2);
v_lhs_472_ = lean_ctor_get(v_c_470_, 0);
v_rhs_473_ = lean_ctor_get(v_c_470_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_c_470_);
if (v_isSharedCheck_485_ == 0)
{
v___x_475_ = v_c_470_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_rhs_473_);
lean_inc(v_lhs_472_);
lean_dec(v_c_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; 
v___x_477_ = l_Nat_Linear_Expr_toNormPoly(v_lhs_472_);
lean_dec_ref(v_lhs_472_);
v___x_478_ = l_Nat_Linear_Expr_toNormPoly(v_rhs_473_);
lean_dec_ref(v_rhs_473_);
v___x_479_ = l_Nat_Linear_Poly_cancel(v___x_477_, v___x_478_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_fst_480_);
v_snd_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_snd_481_);
lean_dec_ref(v___x_479_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_snd_481_);
lean_ctor_set(v___x_475_, 0, v_fst_480_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_fst_480_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_snd_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*2, v_eq_471_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_monomialToExpr(lean_object* v_k_486_, lean_object* v_v_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(100000000u);
v___x_489_ = lean_nat_dec_eq(v_v_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_dec_eq(v_k_486_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_v_487_);
v___x_493_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_493_, 0, v_k_486_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
lean_dec(v_k_486_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_v_487_);
return v___x_494_;
}
}
else
{
lean_object* v___x_495_; 
lean_dec(v_v_487_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_k_486_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr_go(lean_object* v_e_496_, lean_object* v_p_497_){
_start:
{
if (lean_obj_tag(v_p_497_) == 0)
{
return v_e_496_;
}
else
{
lean_object* v_head_498_; lean_object* v_tail_499_; lean_object* v_fst_500_; lean_object* v_snd_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
v_head_498_ = lean_ctor_get(v_p_497_, 0);
lean_inc(v_head_498_);
v_tail_499_ = lean_ctor_get(v_p_497_, 1);
lean_inc(v_tail_499_);
lean_dec_ref(v_p_497_);
v_fst_500_ = lean_ctor_get(v_head_498_, 0);
v_snd_501_ = lean_ctor_get(v_head_498_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_head_498_);
if (v_isSharedCheck_510_ == 0)
{
v___x_503_ = v_head_498_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snd_501_);
lean_inc(v_fst_500_);
lean_dec(v_head_498_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = l_Nat_Linear_monomialToExpr(v_fst_500_, v_snd_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 2);
lean_ctor_set(v___x_503_, 1, v___x_505_);
lean_ctor_set(v___x_503_, 0, v_e_496_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_e_496_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
v_e_496_ = v___x_507_;
v_p_497_ = v_tail_499_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr(lean_object* v_p_511_){
_start:
{
if (lean_obj_tag(v_p_511_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Nat_Linear_instInhabitedExpr_default___closed__0));
return v___x_512_;
}
else
{
lean_object* v_head_513_; lean_object* v_tail_514_; lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_head_513_ = lean_ctor_get(v_p_511_, 0);
lean_inc(v_head_513_);
v_tail_514_ = lean_ctor_get(v_p_511_, 1);
lean_inc(v_tail_514_);
lean_dec_ref(v_p_511_);
v_fst_515_ = lean_ctor_get(v_head_513_, 0);
lean_inc(v_fst_515_);
v_snd_516_ = lean_ctor_get(v_head_513_, 1);
lean_inc(v_snd_516_);
lean_dec(v_head_513_);
v___x_517_ = l_Nat_Linear_monomialToExpr(v_fst_515_, v_snd_516_);
v___x_518_ = l_Nat_Linear_Poly_toExpr_go(v___x_517_, v_tail_514_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object* v_c_519_){
_start:
{
uint8_t v_eq_520_; lean_object* v_lhs_521_; lean_object* v_rhs_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_eq_520_ = lean_ctor_get_uint8(v_c_519_, sizeof(void*)*2);
v_lhs_521_ = lean_ctor_get(v_c_519_, 0);
v_rhs_522_ = lean_ctor_get(v_c_519_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_c_519_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v_c_519_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_rhs_522_);
lean_inc(v_lhs_521_);
lean_dec(v_c_519_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = l_Nat_Linear_Poly_toExpr(v_lhs_521_);
v___x_527_ = l_Nat_Linear_Poly_toExpr(v_rhs_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_527_);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*2, v_eq_520_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(lean_object* v_p_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
if (lean_obj_tag(v_p_532_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_534_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_apply_1(v_h__1_533_, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v_head_537_; lean_object* v_tail_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; 
lean_dec(v_h__1_533_);
v_head_537_ = lean_ctor_get(v_p_532_, 0);
lean_inc(v_head_537_);
v_tail_538_ = lean_ctor_get(v_p_532_, 1);
lean_inc(v_tail_538_);
lean_dec_ref(v_p_532_);
v_fst_539_ = lean_ctor_get(v_head_537_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v_head_537_, 1);
lean_inc(v_snd_540_);
lean_dec(v_head_537_);
v___x_541_ = lean_apply_3(v_h__2_534_, v_fst_539_, v_snd_540_, v_tail_538_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(lean_object* v_motive_542_, lean_object* v_p_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(v_p_543_, v_h__1_544_, v_h__2_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object* v_fuel_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_){
_start:
{
lean_object* v_zero_550_; uint8_t v_isZero_551_; 
v_zero_550_ = lean_unsigned_to_nat(0u);
v_isZero_551_ = lean_nat_dec_eq(v_fuel_547_, v_zero_550_);
if (v_isZero_551_ == 1)
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_h__2_549_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_apply_1(v_h__1_548_, v___x_552_);
return v___x_553_;
}
else
{
lean_object* v_one_554_; lean_object* v_n_555_; lean_object* v___x_556_; 
lean_dec(v_h__1_548_);
v_one_554_ = lean_unsigned_to_nat(1u);
v_n_555_ = lean_nat_sub(v_fuel_547_, v_one_554_);
v___x_556_ = lean_apply_1(v_h__2_549_, v_n_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object* v_fuel_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(v_fuel_557_, v_h__1_558_, v_h__2_559_);
lean_dec(v_fuel_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(lean_object* v_motive_561_, lean_object* v_fuel_562_, lean_object* v_h__1_563_, lean_object* v_h__2_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(v_fuel_562_, v_h__1_563_, v_h__2_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object* v_motive_566_, lean_object* v_fuel_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(v_motive_566_, v_fuel_567_, v_h__1_568_, v_h__2_569_);
lean_dec(v_fuel_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object* v_m_u2081_571_, lean_object* v_m_u2082_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_, lean_object* v_h__3_575_){
_start:
{
if (lean_obj_tag(v_m_u2082_572_) == 0)
{
lean_object* v___x_576_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__2_574_);
v___x_576_ = lean_apply_1(v_h__1_573_, v_m_u2081_571_);
return v___x_576_;
}
else
{
lean_dec(v_h__1_573_);
if (lean_obj_tag(v_m_u2081_571_) == 0)
{
lean_object* v___x_577_; 
lean_dec(v_h__3_575_);
v___x_577_ = lean_apply_2(v_h__2_574_, v_m_u2082_572_, lean_box(0));
return v___x_577_;
}
else
{
lean_object* v_head_578_; lean_object* v_head_579_; lean_object* v_tail_580_; lean_object* v_tail_581_; lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_586_; 
lean_dec(v_h__2_574_);
v_head_578_ = lean_ctor_get(v_m_u2081_571_, 0);
lean_inc(v_head_578_);
v_head_579_ = lean_ctor_get(v_m_u2082_572_, 0);
lean_inc(v_head_579_);
v_tail_580_ = lean_ctor_get(v_m_u2082_572_, 1);
lean_inc(v_tail_580_);
lean_dec_ref(v_m_u2082_572_);
v_tail_581_ = lean_ctor_get(v_m_u2081_571_, 1);
lean_inc(v_tail_581_);
lean_dec_ref(v_m_u2081_571_);
v_fst_582_ = lean_ctor_get(v_head_578_, 0);
lean_inc(v_fst_582_);
v_snd_583_ = lean_ctor_get(v_head_578_, 1);
lean_inc(v_snd_583_);
lean_dec(v_head_578_);
v_fst_584_ = lean_ctor_get(v_head_579_, 0);
lean_inc(v_fst_584_);
v_snd_585_ = lean_ctor_get(v_head_579_, 1);
lean_inc(v_snd_585_);
lean_dec(v_head_579_);
v___x_586_ = lean_apply_6(v_h__3_575_, v_fst_582_, v_snd_583_, v_tail_581_, v_fst_584_, v_snd_585_, v_tail_580_);
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(lean_object* v_motive_587_, lean_object* v_m_u2081_588_, lean_object* v_m_u2082_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_, lean_object* v_h__3_592_){
_start:
{
if (lean_obj_tag(v_m_u2082_589_) == 0)
{
lean_object* v___x_593_; 
lean_dec(v_h__3_592_);
lean_dec(v_h__2_591_);
v___x_593_ = lean_apply_1(v_h__1_590_, v_m_u2081_588_);
return v___x_593_;
}
else
{
lean_dec(v_h__1_590_);
if (lean_obj_tag(v_m_u2081_588_) == 0)
{
lean_object* v___x_594_; 
lean_dec(v_h__3_592_);
v___x_594_ = lean_apply_2(v_h__2_591_, v_m_u2082_589_, lean_box(0));
return v___x_594_;
}
else
{
lean_object* v_head_595_; lean_object* v_head_596_; lean_object* v_tail_597_; lean_object* v_tail_598_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v_fst_601_; lean_object* v_snd_602_; lean_object* v___x_603_; 
lean_dec(v_h__2_591_);
v_head_595_ = lean_ctor_get(v_m_u2081_588_, 0);
lean_inc(v_head_595_);
v_head_596_ = lean_ctor_get(v_m_u2082_589_, 0);
lean_inc(v_head_596_);
v_tail_597_ = lean_ctor_get(v_m_u2082_589_, 1);
lean_inc(v_tail_597_);
lean_dec_ref(v_m_u2082_589_);
v_tail_598_ = lean_ctor_get(v_m_u2081_588_, 1);
lean_inc(v_tail_598_);
lean_dec_ref(v_m_u2081_588_);
v_fst_599_ = lean_ctor_get(v_head_595_, 0);
lean_inc(v_fst_599_);
v_snd_600_ = lean_ctor_get(v_head_595_, 1);
lean_inc(v_snd_600_);
lean_dec(v_head_595_);
v_fst_601_ = lean_ctor_get(v_head_596_, 0);
lean_inc(v_fst_601_);
v_snd_602_ = lean_ctor_get(v_head_596_, 1);
lean_inc(v_snd_602_);
lean_dec(v_head_596_);
v___x_603_ = lean_apply_6(v_h__3_592_, v_fst_599_, v_snd_600_, v_tail_598_, v_fst_601_, v_snd_602_, v_tail_597_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_, lean_object* v_h__3_607_, lean_object* v_h__4_608_, lean_object* v_h__5_609_){
_start:
{
switch(lean_obj_tag(v_x_604_))
{
case 0:
{
lean_object* v_v_610_; lean_object* v___x_611_; 
lean_dec(v_h__5_609_);
lean_dec(v_h__4_608_);
lean_dec(v_h__3_607_);
lean_dec(v_h__2_606_);
v_v_610_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_v_610_);
lean_dec_ref(v_x_604_);
v___x_611_ = lean_apply_1(v_h__1_605_, v_v_610_);
return v___x_611_;
}
case 1:
{
lean_object* v_i_612_; lean_object* v___x_613_; 
lean_dec(v_h__5_609_);
lean_dec(v_h__4_608_);
lean_dec(v_h__3_607_);
lean_dec(v_h__1_605_);
v_i_612_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_i_612_);
lean_dec_ref(v_x_604_);
v___x_613_ = lean_apply_1(v_h__2_606_, v_i_612_);
return v___x_613_;
}
case 2:
{
lean_object* v_a_614_; lean_object* v_b_615_; lean_object* v___x_616_; 
lean_dec(v_h__5_609_);
lean_dec(v_h__4_608_);
lean_dec(v_h__2_606_);
lean_dec(v_h__1_605_);
v_a_614_ = lean_ctor_get(v_x_604_, 0);
lean_inc_ref(v_a_614_);
v_b_615_ = lean_ctor_get(v_x_604_, 1);
lean_inc_ref(v_b_615_);
lean_dec_ref(v_x_604_);
v___x_616_ = lean_apply_2(v_h__3_607_, v_a_614_, v_b_615_);
return v___x_616_;
}
case 3:
{
lean_object* v_k_617_; lean_object* v_a_618_; lean_object* v___x_619_; 
lean_dec(v_h__5_609_);
lean_dec(v_h__3_607_);
lean_dec(v_h__2_606_);
lean_dec(v_h__1_605_);
v_k_617_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_k_617_);
v_a_618_ = lean_ctor_get(v_x_604_, 1);
lean_inc_ref(v_a_618_);
lean_dec_ref(v_x_604_);
v___x_619_ = lean_apply_2(v_h__4_608_, v_k_617_, v_a_618_);
return v___x_619_;
}
default: 
{
lean_object* v_a_620_; lean_object* v_k_621_; lean_object* v___x_622_; 
lean_dec(v_h__4_608_);
lean_dec(v_h__3_607_);
lean_dec(v_h__2_606_);
lean_dec(v_h__1_605_);
v_a_620_ = lean_ctor_get(v_x_604_, 0);
lean_inc_ref(v_a_620_);
v_k_621_ = lean_ctor_get(v_x_604_, 1);
lean_inc(v_k_621_);
lean_dec_ref(v_x_604_);
v___x_622_ = lean_apply_2(v_h__5_609_, v_a_620_, v_k_621_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter(lean_object* v_motive_623_, lean_object* v_x_624_, lean_object* v_h__1_625_, lean_object* v_h__2_626_, lean_object* v_h__3_627_, lean_object* v_h__4_628_, lean_object* v_h__5_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(v_x_624_, v_h__1_625_, v_h__2_626_, v_h__3_627_, v_h__4_628_, v_h__5_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(lean_object* v_p_631_, lean_object* v_h__1_632_, lean_object* v_h__2_633_){
_start:
{
if (lean_obj_tag(v_p_631_) == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v_h__2_633_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_apply_1(v_h__1_632_, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; 
lean_dec(v_h__1_632_);
v___x_636_ = lean_apply_2(v_h__2_633_, v_p_631_, lean_box(0));
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(lean_object* v_motive_637_, lean_object* v_p_638_, lean_object* v_h__1_639_, lean_object* v_h__2_640_){
_start:
{
if (lean_obj_tag(v_p_638_) == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_h__2_640_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_apply_1(v_h__1_639_, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
lean_dec(v_h__1_639_);
v___x_643_ = lean_apply_2(v_h__2_640_, v_p_638_, lean_box(0));
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_elimOffset___redArg(lean_object* v_h_u2082_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_apply_1(v_h_u2082_644_, lean_box(0));
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Nat_elimOffset(lean_object* v_00_u03b1_646_, lean_object* v_a_647_, lean_object* v_b_648_, lean_object* v_k_649_, lean_object* v_h_u2081_650_, lean_object* v_h_u2082_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_apply_1(v_h_u2082_651_, lean_box(0));
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Nat_elimOffset___boxed(lean_object* v_00_u03b1_653_, lean_object* v_a_654_, lean_object* v_b_655_, lean_object* v_k_656_, lean_object* v_h_u2081_657_, lean_object* v_h_u2082_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Nat_elimOffset(v_00_u03b1_653_, v_a_654_, v_b_655_, v_k_656_, v_h_u2081_657_, v_h_u2082_658_);
lean_dec(v_k_656_);
lean_dec(v_b_655_);
lean_dec(v_a_654_);
return v_res_659_;
}
}
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_Nat_Linear_fixedVar = _init_l_Nat_Linear_fixedVar();
lean_mark_persistent(l_Nat_Linear_fixedVar);
l_Nat_Linear_hugeFuel = _init_l_Nat_Linear_hugeFuel();
lean_mark_persistent(l_Nat_Linear_hugeFuel);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Linear(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Linear(builtin);
}
#ifdef __cplusplus
}
#endif
