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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_fixedVar;
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx___impl(lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_tag_nat(v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Nat_Internal_Linear_Expr_ctorIdx___impl(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
switch(lean_obj_tag(v_t_6_))
{
case 2:
{
lean_object* v_a_8_; lean_object* v_b_9_; lean_object* v___x_10_; 
v_a_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_a_8_);
v_b_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_b_9_);
lean_dec_ref_known(v_t_6_, 2);
v___x_10_ = lean_apply_2(v_k_7_, v_a_8_, v_b_9_);
return v___x_10_;
}
case 3:
{
lean_object* v_k_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
v_k_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_k_11_);
v_a_12_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_a_12_);
lean_dec_ref_known(v_t_6_, 2);
v___x_13_ = lean_apply_2(v_k_7_, v_k_11_, v_a_12_);
return v___x_13_;
}
case 4:
{
lean_object* v_a_14_; lean_object* v_k_15_; lean_object* v___x_16_; 
v_a_14_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_a_14_);
v_k_15_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_k_15_);
lean_dec_ref_known(v_t_6_, 2);
v___x_16_ = lean_apply_2(v_k_7_, v_a_14_, v_k_15_);
return v___x_16_;
}
default: 
{
lean_object* v_v_17_; lean_object* v___x_18_; 
v_v_17_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_v_17_);
lean_dec_ref(v_t_6_);
v___x_18_ = lean_apply_1(v_k_7_, v_v_17_);
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Nat_Internal_Linear_Expr_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_num_elim___redArg(lean_object* v_t_31_, lean_object* v_num_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_31_, v_num_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_num_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_num_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_35_, v_num_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_var_elim___redArg(lean_object* v_t_39_, lean_object* v_var_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_39_, v_var_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_var_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_var_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_43_, v_var_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_add_elim___redArg(lean_object* v_t_47_, lean_object* v_add_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_47_, v_add_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_add_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_add_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_51_, v_add_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulL_elim___redArg(lean_object* v_t_55_, lean_object* v_mulL_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_55_, v_mulL_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulL_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_mulL_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_59_, v_mulL_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulR_elim___redArg(lean_object* v_t_63_, lean_object* v_mulR_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_63_, v_mulR_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_mulR_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_mulR_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Nat_Internal_Linear_Expr_ctorElim___redArg(v_t_67_, v_mulR_69_);
return v___x_70_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_instBEqExpr_beq(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_v_77_; lean_object* v_v_78_; uint8_t v___x_79_; 
v_v_77_ = lean_ctor_get(v_x_75_, 0);
v_v_78_ = lean_ctor_get(v_x_76_, 0);
v___x_79_ = lean_nat_dec_eq(v_v_77_, v_v_78_);
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
case 1:
{
if (lean_obj_tag(v_x_76_) == 1)
{
lean_object* v_i_81_; lean_object* v_i_82_; uint8_t v___x_83_; 
v_i_81_ = lean_ctor_get(v_x_75_, 0);
v_i_82_ = lean_ctor_get(v_x_76_, 0);
v___x_83_ = lean_nat_dec_eq(v_i_81_, v_i_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
case 2:
{
if (lean_obj_tag(v_x_76_) == 2)
{
lean_object* v_a_85_; lean_object* v_b_86_; lean_object* v_a_87_; lean_object* v_b_88_; uint8_t v___x_89_; 
v_a_85_ = lean_ctor_get(v_x_75_, 0);
v_b_86_ = lean_ctor_get(v_x_75_, 1);
v_a_87_ = lean_ctor_get(v_x_76_, 0);
v_b_88_ = lean_ctor_get(v_x_76_, 1);
v___x_89_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_a_85_, v_a_87_);
if (v___x_89_ == 0)
{
return v___x_89_;
}
else
{
v_x_75_ = v_b_86_;
v_x_76_ = v_b_88_;
goto _start;
}
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
case 3:
{
if (lean_obj_tag(v_x_76_) == 3)
{
lean_object* v_k_92_; lean_object* v_a_93_; lean_object* v_k_94_; lean_object* v_a_95_; uint8_t v___x_96_; 
v_k_92_ = lean_ctor_get(v_x_75_, 0);
v_a_93_ = lean_ctor_get(v_x_75_, 1);
v_k_94_ = lean_ctor_get(v_x_76_, 0);
v_a_95_ = lean_ctor_get(v_x_76_, 1);
v___x_96_ = lean_nat_dec_eq(v_k_92_, v_k_94_);
if (v___x_96_ == 0)
{
return v___x_96_;
}
else
{
v_x_75_ = v_a_93_;
v_x_76_ = v_a_95_;
goto _start;
}
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
default: 
{
if (lean_obj_tag(v_x_76_) == 4)
{
lean_object* v_a_99_; lean_object* v_k_100_; lean_object* v_a_101_; lean_object* v_k_102_; uint8_t v___x_103_; 
v_a_99_ = lean_ctor_get(v_x_75_, 0);
v_k_100_ = lean_ctor_get(v_x_75_, 1);
v_a_101_ = lean_ctor_get(v_x_76_, 0);
v_k_102_ = lean_ctor_get(v_x_76_, 1);
v___x_103_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_a_99_, v_a_101_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = lean_nat_dec_eq(v_k_100_, v_k_102_);
return v___x_104_;
}
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqExpr_beq___boxed(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_x_106_, v_x_107_);
lean_dec_ref(v_x_107_);
lean_dec_ref(v_x_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_insert(lean_object* v_k_112_, lean_object* v_v_113_, lean_object* v_p_114_){
_start:
{
if (lean_obj_tag(v_p_114_) == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v_k_112_);
lean_ctor_set(v___x_115_, 1, v_v_113_);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_p_114_);
return v___x_116_;
}
else
{
lean_object* v_head_117_; lean_object* v_tail_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; uint8_t v___x_121_; 
v_head_117_ = lean_ctor_get(v_p_114_, 0);
lean_inc(v_head_117_);
v_tail_118_ = lean_ctor_get(v_p_114_, 1);
v_fst_119_ = lean_ctor_get(v_head_117_, 0);
v_snd_120_ = lean_ctor_get(v_head_117_, 1);
v___x_121_ = l_Nat_blt(v_v_113_, v_snd_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_143_; 
lean_inc(v_tail_118_);
v_isSharedCheck_143_ = !lean_is_exclusive(v_p_114_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; lean_object* v_unused_145_; 
v_unused_144_ = lean_ctor_get(v_p_114_, 1);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_p_114_, 0);
lean_dec(v_unused_145_);
v___x_123_ = v_p_114_;
v_isShared_124_ = v_isSharedCheck_143_;
goto v_resetjp_122_;
}
else
{
lean_dec(v_p_114_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_143_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_eq(v_v_113_, v_snd_120_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = l_Nat_Internal_Linear_Poly_insert(v_k_112_, v_v_113_, v_tail_118_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_126_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_head_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_140_; 
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_v_113_);
v_isSharedCheck_140_ = !lean_is_exclusive(v_head_117_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; lean_object* v_unused_142_; 
v_unused_141_ = lean_ctor_get(v_head_117_, 1);
lean_dec(v_unused_141_);
v_unused_142_ = lean_ctor_get(v_head_117_, 0);
lean_dec(v_unused_142_);
v___x_131_ = v_head_117_;
v_isShared_132_ = v_isSharedCheck_140_;
goto v_resetjp_130_;
}
else
{
lean_dec(v_head_117_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_140_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = lean_nat_add(v_k_112_, v_fst_119_);
lean_dec(v_fst_119_);
lean_dec(v_k_112_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_snd_120_);
v___x_135_ = v_reuseFailAlloc_139_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_135_);
v___x_137_ = v___x_123_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_tail_118_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
else
{
lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
v_isSharedCheck_153_ = !lean_is_exclusive(v_head_117_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_154_ = lean_ctor_get(v_head_117_, 1);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_head_117_, 0);
lean_dec(v_unused_155_);
v___x_147_ = v_head_117_;
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
else
{
lean_dec(v_head_117_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v_v_113_);
lean_ctor_set(v___x_147_, 0, v_k_112_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_k_112_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_v_113_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_p_114_);
return v___x_151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm_go(lean_object* v_p_156_, lean_object* v_r_157_){
_start:
{
if (lean_obj_tag(v_p_156_) == 0)
{
return v_r_157_;
}
else
{
lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v_fst_160_; lean_object* v_snd_161_; lean_object* v___x_162_; 
v_head_158_ = lean_ctor_get(v_p_156_, 0);
lean_inc(v_head_158_);
v_tail_159_ = lean_ctor_get(v_p_156_, 1);
lean_inc(v_tail_159_);
lean_dec_ref_known(v_p_156_, 2);
v_fst_160_ = lean_ctor_get(v_head_158_, 0);
lean_inc(v_fst_160_);
v_snd_161_ = lean_ctor_get(v_head_158_, 1);
lean_inc(v_snd_161_);
lean_dec(v_head_158_);
v___x_162_ = l_Nat_Internal_Linear_Poly_insert(v_fst_160_, v_snd_161_, v_r_157_);
v_p_156_ = v_tail_159_;
v_r_157_ = v___x_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm(lean_object* v_p_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_box(0);
v___x_166_ = l_Nat_Internal_Linear_Poly_norm_go(v_p_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancelAux(lean_object* v_fuel_167_, lean_object* v_m_u2081_168_, lean_object* v_m_u2082_169_, lean_object* v_r_u2081_170_, lean_object* v_r_u2082_171_){
_start:
{
lean_object* v_zero_172_; uint8_t v_isZero_173_; 
v_zero_172_ = lean_unsigned_to_nat(0u);
v_isZero_173_ = lean_nat_dec_eq(v_fuel_167_, v_zero_172_);
if (v_isZero_173_ == 1)
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_fuel_167_);
v___x_174_ = l_List_reverse___redArg(v_r_u2081_170_);
v___x_175_ = l_List_appendTR___redArg(v___x_174_, v_m_u2081_168_);
v___x_176_ = l_List_reverse___redArg(v_r_u2082_171_);
v___x_177_ = l_List_appendTR___redArg(v___x_176_, v_m_u2082_169_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_175_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
else
{
if (lean_obj_tag(v_m_u2082_169_) == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_fuel_167_);
v___x_179_ = l_List_reverse___redArg(v_r_u2081_170_);
v___x_180_ = l_List_appendTR___redArg(v___x_179_, v_m_u2081_168_);
v___x_181_ = l_List_reverse___redArg(v_r_u2082_171_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
else
{
if (lean_obj_tag(v_m_u2081_168_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_fuel_167_);
v___x_183_ = l_List_reverse___redArg(v_r_u2081_170_);
v___x_184_ = l_List_reverse___redArg(v_r_u2082_171_);
v___x_185_ = l_List_appendTR___redArg(v___x_184_, v_m_u2082_169_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_183_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
return v___x_186_;
}
else
{
lean_object* v_head_187_; lean_object* v_head_188_; lean_object* v_tail_189_; lean_object* v_tail_190_; lean_object* v_fst_191_; lean_object* v_snd_192_; lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v_one_195_; lean_object* v_n_196_; uint8_t v___x_197_; 
v_head_187_ = lean_ctor_get(v_m_u2081_168_, 0);
v_head_188_ = lean_ctor_get(v_m_u2082_169_, 0);
lean_inc(v_head_188_);
v_tail_189_ = lean_ctor_get(v_m_u2082_169_, 1);
v_tail_190_ = lean_ctor_get(v_m_u2081_168_, 1);
v_fst_191_ = lean_ctor_get(v_head_187_, 0);
v_snd_192_ = lean_ctor_get(v_head_187_, 1);
v_fst_193_ = lean_ctor_get(v_head_188_, 0);
v_snd_194_ = lean_ctor_get(v_head_188_, 1);
v_one_195_ = lean_unsigned_to_nat(1u);
v_n_196_ = lean_nat_sub(v_fuel_167_, v_one_195_);
lean_dec(v_fuel_167_);
v___x_197_ = l_Nat_blt(v_snd_192_, v_snd_194_);
if (v___x_197_ == 0)
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_237_; 
lean_inc(v_tail_189_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_m_u2082_169_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; 
v_unused_238_ = lean_ctor_get(v_m_u2082_169_, 1);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_m_u2082_169_, 0);
lean_dec(v_unused_239_);
v___x_199_ = v_m_u2082_169_;
v_isShared_200_ = v_isSharedCheck_237_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_m_u2082_169_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_237_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
uint8_t v___x_201_; 
v___x_201_ = l_Nat_blt(v_snd_194_, v_snd_192_);
if (v___x_201_ == 0)
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_230_; 
lean_inc(v_fst_193_);
lean_inc(v_snd_192_);
lean_inc(v_fst_191_);
lean_inc(v_tail_190_);
lean_del_object(v___x_199_);
v_isSharedCheck_230_ = !lean_is_exclusive(v_m_u2081_168_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_231_ = lean_ctor_get(v_m_u2081_168_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_m_u2081_168_, 0);
lean_dec(v_unused_232_);
v___x_203_ = v_m_u2081_168_;
v_isShared_204_ = v_isSharedCheck_230_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_m_u2081_168_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_230_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_227_; 
v_isSharedCheck_227_ = !lean_is_exclusive(v_head_188_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; lean_object* v_unused_229_; 
v_unused_228_ = lean_ctor_get(v_head_188_, 1);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_head_188_, 0);
lean_dec(v_unused_229_);
v___x_206_ = v_head_188_;
v_isShared_207_ = v_isSharedCheck_227_;
goto v_resetjp_205_;
}
else
{
lean_dec(v_head_188_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_227_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
uint8_t v___x_208_; 
v___x_208_ = l_Nat_blt(v_fst_191_, v_fst_193_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
v___x_209_ = l_Nat_blt(v_fst_193_, v_fst_191_);
if (v___x_209_ == 0)
{
lean_del_object(v___x_206_);
lean_del_object(v___x_203_);
lean_dec(v_fst_193_);
lean_dec(v_snd_192_);
lean_dec(v_fst_191_);
v_fuel_167_ = v_n_196_;
v_m_u2081_168_ = v_tail_190_;
v_m_u2082_169_ = v_tail_189_;
goto _start;
}
else
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_nat_sub(v_fst_191_, v_fst_193_);
lean_dec(v_fst_193_);
lean_dec(v_fst_191_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v_snd_192_);
lean_ctor_set(v___x_206_, 0, v___x_211_);
v___x_213_ = v___x_206_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_snd_192_);
v___x_213_ = v_reuseFailAlloc_218_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_r_u2081_170_);
lean_ctor_set(v___x_203_, 0, v___x_213_);
v___x_215_ = v___x_203_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_r_u2081_170_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v_fuel_167_ = v_n_196_;
v_m_u2081_168_ = v_tail_190_;
v_m_u2082_169_ = v_tail_189_;
v_r_u2081_170_ = v___x_215_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_nat_sub(v_fst_193_, v_fst_191_);
lean_dec(v_fst_191_);
lean_dec(v_fst_193_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v_snd_192_);
lean_ctor_set(v___x_206_, 0, v___x_219_);
v___x_221_ = v___x_206_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_snd_192_);
v___x_221_ = v_reuseFailAlloc_226_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_r_u2082_171_);
lean_ctor_set(v___x_203_, 0, v___x_221_);
v___x_223_ = v___x_203_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_r_u2082_171_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
v_fuel_167_ = v_n_196_;
v_m_u2081_168_ = v_tail_190_;
v_m_u2082_169_ = v_tail_189_;
v_r_u2082_171_ = v___x_223_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_234_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v_r_u2082_171_);
v___x_234_ = v___x_199_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_head_188_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_r_u2082_171_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
v_fuel_167_ = v_n_196_;
v_m_u2082_169_ = v_tail_189_;
v_r_u2082_171_ = v___x_234_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
lean_inc(v_tail_190_);
lean_inc(v_head_187_);
lean_dec(v_head_188_);
v_isSharedCheck_247_ = !lean_is_exclusive(v_m_u2081_168_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_248_ = lean_ctor_get(v_m_u2081_168_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_m_u2081_168_, 0);
lean_dec(v_unused_249_);
v___x_241_ = v_m_u2081_168_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_dec(v_m_u2081_168_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_r_u2081_170_);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_head_187_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_r_u2081_170_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
v_fuel_167_ = v_n_196_;
v_m_u2081_168_ = v_tail_190_;
v_r_u2081_170_ = v___x_244_;
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
lean_object* v___x_250_; 
v___x_250_ = lean_unsigned_to_nat(1000000u);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancel(lean_object* v_p_u2081_251_, lean_object* v_p_u2082_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(1000000u);
v___x_254_ = lean_box(0);
v___x_255_ = l_Nat_Internal_Linear_Poly_cancelAux(v___x_253_, v_p_u2081_251_, v_p_u2082_252_, v___x_254_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f(lean_object* v_p_258_){
_start:
{
if (lean_obj_tag(v_p_258_) == 0)
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_Nat_Internal_Linear_Poly_isNum_x3f___closed__0));
return v___x_259_;
}
else
{
lean_object* v_tail_260_; 
v_tail_260_ = lean_ctor_get(v_p_258_, 1);
if (lean_obj_tag(v_tail_260_) == 0)
{
lean_object* v_head_261_; lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_head_261_ = lean_ctor_get(v_p_258_, 0);
v_fst_262_ = lean_ctor_get(v_head_261_, 0);
v_snd_263_ = lean_ctor_get(v_head_261_, 1);
v___x_264_ = lean_unsigned_to_nat(100000000u);
v___x_265_ = lean_nat_dec_eq(v_snd_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
lean_inc(v_fst_262_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_fst_262_);
return v___x_267_;
}
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f___boxed(lean_object* v_p_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Nat_Internal_Linear_Poly_isNum_x3f(v_p_269_);
lean_dec(v_p_269_);
return v_res_270_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_Poly_isZero(lean_object* v_p_271_){
_start:
{
if (lean_obj_tag(v_p_271_) == 0)
{
uint8_t v___x_272_; 
v___x_272_ = 1;
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = 0;
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isZero___boxed(lean_object* v_p_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Nat_Internal_Linear_Poly_isZero(v_p_274_);
lean_dec(v_p_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_Poly_isNonZero(lean_object* v_p_277_){
_start:
{
if (lean_obj_tag(v_p_277_) == 0)
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
else
{
lean_object* v_head_279_; lean_object* v_tail_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_head_279_ = lean_ctor_get(v_p_277_, 0);
v_tail_280_ = lean_ctor_get(v_p_277_, 1);
v_fst_281_ = lean_ctor_get(v_head_279_, 0);
v_snd_282_ = lean_ctor_get(v_head_279_, 1);
v___x_283_ = lean_unsigned_to_nat(100000000u);
v___x_284_ = lean_nat_dec_eq(v_snd_282_, v___x_283_);
if (v___x_284_ == 0)
{
v_p_277_ = v_tail_280_;
goto _start;
}
else
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_lt(v___x_286_, v_fst_281_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNonZero___boxed(lean_object* v_p_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Nat_Internal_Linear_Poly_isNonZero(v_p_288_);
lean_dec(v_p_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go(lean_object* v_coeff_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
switch(lean_obj_tag(v_a_292_))
{
case 0:
{
lean_object* v_v_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_v_294_ = lean_ctor_get(v_a_292_, 0);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_nat_dec_eq(v_v_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_nat_mul(v_coeff_291_, v_v_294_);
lean_dec(v_coeff_291_);
v___x_298_ = lean_unsigned_to_nat(100000000u);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_a_293_);
return v___x_300_;
}
else
{
lean_dec(v_coeff_291_);
return v_a_293_;
}
}
case 1:
{
lean_object* v_i_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_i_301_ = lean_ctor_get(v_a_292_, 0);
lean_inc(v_i_301_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_coeff_291_);
lean_ctor_set(v___x_302_, 1, v_i_301_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_293_);
return v___x_303_;
}
case 2:
{
lean_object* v_a_304_; lean_object* v_b_305_; lean_object* v___x_306_; 
v_a_304_ = lean_ctor_get(v_a_292_, 0);
v_b_305_ = lean_ctor_get(v_a_292_, 1);
lean_inc(v_coeff_291_);
v___x_306_ = l_Nat_Internal_Linear_Expr_toPoly_go(v_coeff_291_, v_b_305_, v_a_293_);
v_a_292_ = v_a_304_;
v_a_293_ = v___x_306_;
goto _start;
}
case 3:
{
lean_object* v_k_308_; lean_object* v_a_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_k_308_ = lean_ctor_get(v_a_292_, 0);
v_a_309_ = lean_ctor_get(v_a_292_, 1);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_nat_dec_eq(v_k_308_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_nat_mul(v_coeff_291_, v_k_308_);
lean_dec(v_coeff_291_);
v_coeff_291_ = v___x_312_;
v_a_292_ = v_a_309_;
goto _start;
}
else
{
lean_dec(v_coeff_291_);
return v_a_293_;
}
}
default: 
{
lean_object* v_a_314_; lean_object* v_k_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_a_314_ = lean_ctor_get(v_a_292_, 0);
v_k_315_ = lean_ctor_get(v_a_292_, 1);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_nat_dec_eq(v_k_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_nat_mul(v_coeff_291_, v_k_315_);
lean_dec(v_coeff_291_);
v_coeff_291_ = v___x_318_;
v_a_292_ = v_a_314_;
goto _start;
}
else
{
lean_dec(v_coeff_291_);
return v_a_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go___boxed(lean_object* v_coeff_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Nat_Internal_Linear_Expr_toPoly_go(v_coeff_320_, v_a_321_, v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly(lean_object* v_e_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_box(0);
v___x_327_ = l_Nat_Internal_Linear_Expr_toPoly_go(v___x_325_, v_e_324_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly___boxed(lean_object* v_e_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Nat_Internal_Linear_Expr_toPoly(v_e_328_);
lean_dec_ref(v_e_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly(lean_object* v_e_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = l_Nat_Internal_Linear_Expr_toPoly(v_e_330_);
v___x_332_ = l_Nat_Internal_Linear_Poly_norm(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly___boxed(lean_object* v_e_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_e_333_);
lean_dec_ref(v_e_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_inc(lean_object* v_e_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Nat_Internal_Linear_Expr_inc___closed__0));
v___x_339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_339_, 0, v_e_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v___x_342_; 
v___x_342_ = 1;
return v___x_342_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = 0;
return v___x_343_;
}
}
else
{
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v___x_344_; 
v___x_344_ = 0;
return v___x_344_;
}
else
{
lean_object* v_head_345_; lean_object* v_head_346_; lean_object* v_tail_347_; lean_object* v_tail_348_; lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; uint8_t v___x_353_; 
v_head_345_ = lean_ctor_get(v_x_340_, 0);
v_head_346_ = lean_ctor_get(v_x_341_, 0);
v_tail_347_ = lean_ctor_get(v_x_340_, 1);
v_tail_348_ = lean_ctor_get(v_x_341_, 1);
v_fst_349_ = lean_ctor_get(v_head_345_, 0);
v_snd_350_ = lean_ctor_get(v_head_345_, 1);
v_fst_351_ = lean_ctor_get(v_head_346_, 0);
v_snd_352_ = lean_ctor_get(v_head_346_, 1);
v___x_353_ = lean_nat_dec_eq(v_fst_349_, v_fst_351_);
if (v___x_353_ == 0)
{
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_eq(v_snd_350_, v_snd_352_);
if (v___x_354_ == 0)
{
return v___x_354_;
}
else
{
v_x_340_ = v_tail_347_;
v_x_341_ = v_tail_348_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_x_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec(v_x_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_instBEqPolyCnstr_beq(lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_eq_362_; lean_object* v_lhs_363_; lean_object* v_rhs_364_; uint8_t v_eq_365_; lean_object* v_lhs_366_; lean_object* v_rhs_367_; 
v_eq_362_ = lean_ctor_get_uint8(v_x_360_, sizeof(void*)*2);
v_lhs_363_ = lean_ctor_get(v_x_360_, 0);
v_rhs_364_ = lean_ctor_get(v_x_360_, 1);
v_eq_365_ = lean_ctor_get_uint8(v_x_361_, sizeof(void*)*2);
v_lhs_366_ = lean_ctor_get(v_x_361_, 0);
v_rhs_367_ = lean_ctor_get(v_x_361_, 1);
if (v_eq_365_ == 0)
{
if (v_eq_362_ == 0)
{
goto v___jp_368_;
}
else
{
return v_eq_365_;
}
}
else
{
if (v_eq_362_ == 0)
{
return v_eq_362_;
}
else
{
goto v___jp_368_;
}
}
v___jp_368_:
{
uint8_t v___x_369_; 
v___x_369_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_lhs_363_, v_lhs_366_);
if (v___x_369_ == 0)
{
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_rhs_364_, v_rhs_367_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqPolyCnstr_beq___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Nat_Internal_Linear_instBEqPolyCnstr_beq(v_x_371_, v_x_372_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_norm(lean_object* v_c_377_){
_start:
{
uint8_t v_eq_378_; lean_object* v_lhs_379_; lean_object* v_rhs_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
v_eq_378_ = lean_ctor_get_uint8(v_c_377_, sizeof(void*)*2);
v_lhs_379_ = lean_ctor_get(v_c_377_, 0);
v_rhs_380_ = lean_ctor_get(v_c_377_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_c_377_);
if (v_isSharedCheck_392_ == 0)
{
v___x_382_ = v_c_377_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_rhs_380_);
lean_inc(v_lhs_379_);
lean_dec(v_c_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_390_; 
v___x_384_ = l_Nat_Internal_Linear_Poly_norm(v_lhs_379_);
v___x_385_ = l_Nat_Internal_Linear_Poly_norm(v_rhs_380_);
v___x_386_ = l_Nat_Internal_Linear_Poly_cancel(v___x_384_, v___x_385_);
v_fst_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_fst_387_);
v_snd_388_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_snd_388_);
lean_dec_ref(v___x_386_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v_snd_388_);
lean_ctor_set(v___x_382_, 0, v_fst_387_);
v___x_390_ = v___x_382_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_fst_387_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_snd_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_391_, sizeof(void*)*2, v_eq_378_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_PolyCnstr_isUnsat(lean_object* v_c_393_){
_start:
{
uint8_t v_eq_394_; lean_object* v_lhs_395_; lean_object* v_rhs_396_; 
v_eq_394_ = lean_ctor_get_uint8(v_c_393_, sizeof(void*)*2);
v_lhs_395_ = lean_ctor_get(v_c_393_, 0);
v_rhs_396_ = lean_ctor_get(v_c_393_, 1);
if (v_eq_394_ == 0)
{
uint8_t v___x_400_; 
v___x_400_ = l_Nat_Internal_Linear_Poly_isNonZero(v_lhs_395_);
if (v___x_400_ == 0)
{
return v___x_400_;
}
else
{
uint8_t v___x_401_; 
v___x_401_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_396_);
return v___x_401_;
}
}
else
{
uint8_t v___x_402_; 
v___x_402_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_395_);
if (v___x_402_ == 0)
{
goto v___jp_397_;
}
else
{
uint8_t v___x_403_; 
v___x_403_ = l_Nat_Internal_Linear_Poly_isNonZero(v_rhs_396_);
if (v___x_403_ == 0)
{
goto v___jp_397_;
}
else
{
return v___x_403_;
}
}
}
v___jp_397_:
{
uint8_t v___x_398_; 
v___x_398_ = l_Nat_Internal_Linear_Poly_isNonZero(v_lhs_395_);
if (v___x_398_ == 0)
{
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_396_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isUnsat___boxed(lean_object* v_c_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Nat_Internal_Linear_PolyCnstr_isUnsat(v_c_404_);
lean_dec_ref(v_c_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Nat_Internal_Linear_PolyCnstr_isValid(lean_object* v_c_407_){
_start:
{
uint8_t v_eq_408_; 
v_eq_408_ = lean_ctor_get_uint8(v_c_407_, sizeof(void*)*2);
if (v_eq_408_ == 0)
{
lean_object* v_lhs_409_; uint8_t v___x_410_; 
v_lhs_409_ = lean_ctor_get(v_c_407_, 0);
v___x_410_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_409_);
return v___x_410_;
}
else
{
lean_object* v_lhs_411_; lean_object* v_rhs_412_; uint8_t v___x_413_; 
v_lhs_411_ = lean_ctor_get(v_c_407_, 0);
v_rhs_412_ = lean_ctor_get(v_c_407_, 1);
v___x_413_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_411_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_412_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isValid___boxed(lean_object* v_c_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Nat_Internal_Linear_PolyCnstr_isValid(v_c_415_);
lean_dec_ref(v_c_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toPoly(lean_object* v_c_418_){
_start:
{
uint8_t v_eq_419_; lean_object* v_lhs_420_; lean_object* v_rhs_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_430_; 
v_eq_419_ = lean_ctor_get_uint8(v_c_418_, sizeof(void*)*2);
v_lhs_420_ = lean_ctor_get(v_c_418_, 0);
v_rhs_421_ = lean_ctor_get(v_c_418_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_c_418_);
if (v_isSharedCheck_430_ == 0)
{
v___x_423_ = v_c_418_;
v_isShared_424_ = v_isSharedCheck_430_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_rhs_421_);
lean_inc(v_lhs_420_);
lean_dec(v_c_418_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_430_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_425_ = l_Nat_Internal_Linear_Expr_toPoly(v_lhs_420_);
lean_dec_ref(v_lhs_420_);
v___x_426_ = l_Nat_Internal_Linear_Expr_toPoly(v_rhs_421_);
lean_dec_ref(v_rhs_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_426_);
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*2, v_eq_419_);
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
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toNormPoly(lean_object* v_c_431_){
_start:
{
uint8_t v_eq_432_; lean_object* v_lhs_433_; lean_object* v_rhs_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_446_; 
v_eq_432_ = lean_ctor_get_uint8(v_c_431_, sizeof(void*)*2);
v_lhs_433_ = lean_ctor_get(v_c_431_, 0);
v_rhs_434_ = lean_ctor_get(v_c_431_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_c_431_);
if (v_isSharedCheck_446_ == 0)
{
v___x_436_ = v_c_431_;
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_rhs_434_);
lean_inc(v_lhs_433_);
lean_dec(v_c_431_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_444_; 
v___x_438_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_lhs_433_);
lean_dec_ref(v_lhs_433_);
v___x_439_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_rhs_434_);
lean_dec_ref(v_rhs_434_);
v___x_440_ = l_Nat_Internal_Linear_Poly_cancel(v___x_438_, v___x_439_);
v_fst_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_fst_441_);
v_snd_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_snd_442_);
lean_dec_ref(v___x_440_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v_snd_442_);
lean_ctor_set(v___x_436_, 0, v_fst_441_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fst_441_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_snd_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*2, v_eq_432_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_monomialToExpr(lean_object* v_k_447_, lean_object* v_v_448_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(100000000u);
v___x_450_ = lean_nat_dec_eq(v_v_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_dec_eq(v_k_447_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_v_448_);
v___x_454_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_454_, 0, v_k_447_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
lean_dec(v_k_447_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_v_448_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_v_448_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v_k_447_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr_go(lean_object* v_e_457_, lean_object* v_p_458_){
_start:
{
if (lean_obj_tag(v_p_458_) == 0)
{
return v_e_457_;
}
else
{
lean_object* v_head_459_; lean_object* v_tail_460_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
v_head_459_ = lean_ctor_get(v_p_458_, 0);
lean_inc(v_head_459_);
v_tail_460_ = lean_ctor_get(v_p_458_, 1);
lean_inc(v_tail_460_);
lean_dec_ref_known(v_p_458_, 2);
v_fst_461_ = lean_ctor_get(v_head_459_, 0);
v_snd_462_ = lean_ctor_get(v_head_459_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_head_459_);
if (v_isSharedCheck_471_ == 0)
{
v___x_464_ = v_head_459_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v_head_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_Nat_Internal_Linear_monomialToExpr(v_fst_461_, v_snd_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 2);
lean_ctor_set(v___x_464_, 1, v___x_466_);
lean_ctor_set(v___x_464_, 0, v_e_457_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_e_457_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v_e_457_ = v___x_468_;
v_p_458_ = v_tail_460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr(lean_object* v_p_472_){
_start:
{
if (lean_obj_tag(v_p_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0));
return v___x_473_;
}
else
{
lean_object* v_head_474_; lean_object* v_tail_475_; lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_head_474_ = lean_ctor_get(v_p_472_, 0);
lean_inc(v_head_474_);
v_tail_475_ = lean_ctor_get(v_p_472_, 1);
lean_inc(v_tail_475_);
lean_dec_ref_known(v_p_472_, 2);
v_fst_476_ = lean_ctor_get(v_head_474_, 0);
lean_inc(v_fst_476_);
v_snd_477_ = lean_ctor_get(v_head_474_, 1);
lean_inc(v_snd_477_);
lean_dec(v_head_474_);
v___x_478_ = l_Nat_Internal_Linear_monomialToExpr(v_fst_476_, v_snd_477_);
v___x_479_ = l_Nat_Internal_Linear_Poly_toExpr_go(v___x_478_, v_tail_475_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_toExpr(lean_object* v_c_480_){
_start:
{
uint8_t v_eq_481_; lean_object* v_lhs_482_; lean_object* v_rhs_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_492_; 
v_eq_481_ = lean_ctor_get_uint8(v_c_480_, sizeof(void*)*2);
v_lhs_482_ = lean_ctor_get(v_c_480_, 0);
v_rhs_483_ = lean_ctor_get(v_c_480_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_c_480_);
if (v_isSharedCheck_492_ == 0)
{
v___x_485_ = v_c_480_;
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_rhs_483_);
lean_inc(v_lhs_482_);
lean_dec(v_c_480_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = l_Nat_Internal_Linear_Poly_toExpr(v_lhs_482_);
v___x_488_ = l_Nat_Internal_Linear_Poly_toExpr(v_rhs_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_488_);
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*2, v_eq_481_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object* v_fuel_493_, lean_object* v_h__1_494_, lean_object* v_h__2_495_){
_start:
{
lean_object* v_zero_496_; uint8_t v_isZero_497_; 
v_zero_496_ = lean_unsigned_to_nat(0u);
v_isZero_497_ = lean_nat_dec_eq(v_fuel_493_, v_zero_496_);
if (v_isZero_497_ == 1)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_h__2_495_);
v___x_498_ = lean_box(0);
v___x_499_ = lean_apply_1(v_h__1_494_, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_one_500_; lean_object* v_n_501_; lean_object* v___x_502_; 
lean_dec(v_h__1_494_);
v_one_500_ = lean_unsigned_to_nat(1u);
v_n_501_ = lean_nat_sub(v_fuel_493_, v_one_500_);
v___x_502_ = lean_apply_1(v_h__2_495_, v_n_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object* v_fuel_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(v_fuel_503_, v_h__1_504_, v_h__2_505_);
lean_dec(v_fuel_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(lean_object* v_motive_507_, lean_object* v_fuel_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
lean_object* v_zero_511_; uint8_t v_isZero_512_; 
v_zero_511_ = lean_unsigned_to_nat(0u);
v_isZero_512_ = lean_nat_dec_eq(v_fuel_508_, v_zero_511_);
if (v_isZero_512_ == 1)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_510_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_apply_1(v_h__1_509_, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_one_515_; lean_object* v_n_516_; lean_object* v___x_517_; 
lean_dec(v_h__1_509_);
v_one_515_ = lean_unsigned_to_nat(1u);
v_n_516_ = lean_nat_sub(v_fuel_508_, v_one_515_);
v___x_517_ = lean_apply_1(v_h__2_510_, v_n_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object* v_motive_518_, lean_object* v_fuel_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(v_motive_518_, v_fuel_519_, v_h__1_520_, v_h__2_521_);
lean_dec(v_fuel_519_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object* v_m_u2081_523_, lean_object* v_m_u2082_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_){
_start:
{
if (lean_obj_tag(v_m_u2082_524_) == 0)
{
lean_object* v___x_528_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
v___x_528_ = lean_apply_1(v_h__1_525_, v_m_u2081_523_);
return v___x_528_;
}
else
{
lean_dec(v_h__1_525_);
if (lean_obj_tag(v_m_u2081_523_) == 0)
{
lean_object* v___x_529_; 
lean_dec(v_h__3_527_);
v___x_529_ = lean_apply_2(v_h__2_526_, v_m_u2082_524_, lean_box(0));
return v___x_529_;
}
else
{
lean_object* v_head_530_; lean_object* v_head_531_; lean_object* v_tail_532_; lean_object* v_tail_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_538_; 
lean_dec(v_h__2_526_);
v_head_530_ = lean_ctor_get(v_m_u2081_523_, 0);
lean_inc(v_head_530_);
v_head_531_ = lean_ctor_get(v_m_u2082_524_, 0);
lean_inc(v_head_531_);
v_tail_532_ = lean_ctor_get(v_m_u2082_524_, 1);
lean_inc(v_tail_532_);
lean_dec_ref_known(v_m_u2082_524_, 2);
v_tail_533_ = lean_ctor_get(v_m_u2081_523_, 1);
lean_inc(v_tail_533_);
lean_dec_ref_known(v_m_u2081_523_, 2);
v_fst_534_ = lean_ctor_get(v_head_530_, 0);
lean_inc(v_fst_534_);
v_snd_535_ = lean_ctor_get(v_head_530_, 1);
lean_inc(v_snd_535_);
lean_dec(v_head_530_);
v_fst_536_ = lean_ctor_get(v_head_531_, 0);
lean_inc(v_fst_536_);
v_snd_537_ = lean_ctor_get(v_head_531_, 1);
lean_inc(v_snd_537_);
lean_dec(v_head_531_);
v___x_538_ = lean_apply_6(v_h__3_527_, v_fst_534_, v_snd_535_, v_tail_533_, v_fst_536_, v_snd_537_, v_tail_532_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter(lean_object* v_motive_539_, lean_object* v_m_u2081_540_, lean_object* v_m_u2082_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_, lean_object* v_h__3_544_){
_start:
{
if (lean_obj_tag(v_m_u2082_541_) == 0)
{
lean_object* v___x_545_; 
lean_dec(v_h__3_544_);
lean_dec(v_h__2_543_);
v___x_545_ = lean_apply_1(v_h__1_542_, v_m_u2081_540_);
return v___x_545_;
}
else
{
lean_dec(v_h__1_542_);
if (lean_obj_tag(v_m_u2081_540_) == 0)
{
lean_object* v___x_546_; 
lean_dec(v_h__3_544_);
v___x_546_ = lean_apply_2(v_h__2_543_, v_m_u2082_541_, lean_box(0));
return v___x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v_tail_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v_fst_553_; lean_object* v_snd_554_; lean_object* v___x_555_; 
lean_dec(v_h__2_543_);
v_head_547_ = lean_ctor_get(v_m_u2081_540_, 0);
lean_inc(v_head_547_);
v_head_548_ = lean_ctor_get(v_m_u2082_541_, 0);
lean_inc(v_head_548_);
v_tail_549_ = lean_ctor_get(v_m_u2082_541_, 1);
lean_inc(v_tail_549_);
lean_dec_ref_known(v_m_u2082_541_, 2);
v_tail_550_ = lean_ctor_get(v_m_u2081_540_, 1);
lean_inc(v_tail_550_);
lean_dec_ref_known(v_m_u2081_540_, 2);
v_fst_551_ = lean_ctor_get(v_head_547_, 0);
lean_inc(v_fst_551_);
v_snd_552_ = lean_ctor_get(v_head_547_, 1);
lean_inc(v_snd_552_);
lean_dec(v_head_547_);
v_fst_553_ = lean_ctor_get(v_head_548_, 0);
lean_inc(v_fst_553_);
v_snd_554_ = lean_ctor_get(v_head_548_, 1);
lean_inc(v_snd_554_);
lean_dec(v_head_548_);
v___x_555_ = lean_apply_6(v_h__3_544_, v_fst_551_, v_snd_552_, v_tail_550_, v_fst_553_, v_snd_554_, v_tail_549_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object* v_x_556_, lean_object* v_h__1_557_, lean_object* v_h__2_558_, lean_object* v_h__3_559_, lean_object* v_h__4_560_, lean_object* v_h__5_561_){
_start:
{
switch(lean_obj_tag(v_x_556_))
{
case 0:
{
lean_object* v_v_562_; lean_object* v___x_563_; 
lean_dec(v_h__5_561_);
lean_dec(v_h__4_560_);
lean_dec(v_h__3_559_);
lean_dec(v_h__2_558_);
v_v_562_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_v_562_);
lean_dec_ref_known(v_x_556_, 1);
v___x_563_ = lean_apply_1(v_h__1_557_, v_v_562_);
return v___x_563_;
}
case 1:
{
lean_object* v_i_564_; lean_object* v___x_565_; 
lean_dec(v_h__5_561_);
lean_dec(v_h__4_560_);
lean_dec(v_h__3_559_);
lean_dec(v_h__1_557_);
v_i_564_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_i_564_);
lean_dec_ref_known(v_x_556_, 1);
v___x_565_ = lean_apply_1(v_h__2_558_, v_i_564_);
return v___x_565_;
}
case 2:
{
lean_object* v_a_566_; lean_object* v_b_567_; lean_object* v___x_568_; 
lean_dec(v_h__5_561_);
lean_dec(v_h__4_560_);
lean_dec(v_h__2_558_);
lean_dec(v_h__1_557_);
v_a_566_ = lean_ctor_get(v_x_556_, 0);
lean_inc_ref(v_a_566_);
v_b_567_ = lean_ctor_get(v_x_556_, 1);
lean_inc_ref(v_b_567_);
lean_dec_ref_known(v_x_556_, 2);
v___x_568_ = lean_apply_2(v_h__3_559_, v_a_566_, v_b_567_);
return v___x_568_;
}
case 3:
{
lean_object* v_k_569_; lean_object* v_a_570_; lean_object* v___x_571_; 
lean_dec(v_h__5_561_);
lean_dec(v_h__3_559_);
lean_dec(v_h__2_558_);
lean_dec(v_h__1_557_);
v_k_569_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_k_569_);
v_a_570_ = lean_ctor_get(v_x_556_, 1);
lean_inc_ref(v_a_570_);
lean_dec_ref_known(v_x_556_, 2);
v___x_571_ = lean_apply_2(v_h__4_560_, v_k_569_, v_a_570_);
return v___x_571_;
}
default: 
{
lean_object* v_a_572_; lean_object* v_k_573_; lean_object* v___x_574_; 
lean_dec(v_h__4_560_);
lean_dec(v_h__3_559_);
lean_dec(v_h__2_558_);
lean_dec(v_h__1_557_);
v_a_572_ = lean_ctor_get(v_x_556_, 0);
lean_inc_ref(v_a_572_);
v_k_573_ = lean_ctor_get(v_x_556_, 1);
lean_inc(v_k_573_);
lean_dec_ref_known(v_x_556_, 2);
v___x_574_ = lean_apply_2(v_h__5_561_, v_a_572_, v_k_573_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter(lean_object* v_motive_575_, lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_, lean_object* v_h__3_579_, lean_object* v_h__4_580_, lean_object* v_h__5_581_){
_start:
{
switch(lean_obj_tag(v_x_576_))
{
case 0:
{
lean_object* v_v_582_; lean_object* v___x_583_; 
lean_dec(v_h__5_581_);
lean_dec(v_h__4_580_);
lean_dec(v_h__3_579_);
lean_dec(v_h__2_578_);
v_v_582_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_v_582_);
lean_dec_ref_known(v_x_576_, 1);
v___x_583_ = lean_apply_1(v_h__1_577_, v_v_582_);
return v___x_583_;
}
case 1:
{
lean_object* v_i_584_; lean_object* v___x_585_; 
lean_dec(v_h__5_581_);
lean_dec(v_h__4_580_);
lean_dec(v_h__3_579_);
lean_dec(v_h__1_577_);
v_i_584_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_i_584_);
lean_dec_ref_known(v_x_576_, 1);
v___x_585_ = lean_apply_1(v_h__2_578_, v_i_584_);
return v___x_585_;
}
case 2:
{
lean_object* v_a_586_; lean_object* v_b_587_; lean_object* v___x_588_; 
lean_dec(v_h__5_581_);
lean_dec(v_h__4_580_);
lean_dec(v_h__2_578_);
lean_dec(v_h__1_577_);
v_a_586_ = lean_ctor_get(v_x_576_, 0);
lean_inc_ref(v_a_586_);
v_b_587_ = lean_ctor_get(v_x_576_, 1);
lean_inc_ref(v_b_587_);
lean_dec_ref_known(v_x_576_, 2);
v___x_588_ = lean_apply_2(v_h__3_579_, v_a_586_, v_b_587_);
return v___x_588_;
}
case 3:
{
lean_object* v_k_589_; lean_object* v_a_590_; lean_object* v___x_591_; 
lean_dec(v_h__5_581_);
lean_dec(v_h__3_579_);
lean_dec(v_h__2_578_);
lean_dec(v_h__1_577_);
v_k_589_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_k_589_);
v_a_590_ = lean_ctor_get(v_x_576_, 1);
lean_inc_ref(v_a_590_);
lean_dec_ref_known(v_x_576_, 2);
v___x_591_ = lean_apply_2(v_h__4_580_, v_k_589_, v_a_590_);
return v___x_591_;
}
default: 
{
lean_object* v_a_592_; lean_object* v_k_593_; lean_object* v___x_594_; 
lean_dec(v_h__4_580_);
lean_dec(v_h__3_579_);
lean_dec(v_h__2_578_);
lean_dec(v_h__1_577_);
v_a_592_ = lean_ctor_get(v_x_576_, 0);
lean_inc_ref(v_a_592_);
v_k_593_ = lean_ctor_get(v_x_576_, 1);
lean_inc(v_k_593_);
lean_dec_ref_known(v_x_576_, 2);
v___x_594_ = lean_apply_2(v_h__5_581_, v_a_592_, v_k_593_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter___redArg(lean_object* v_p_595_, lean_object* v_h__1_596_, lean_object* v_h__2_597_){
_start:
{
if (lean_obj_tag(v_p_595_) == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_h__2_597_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_apply_1(v_h__1_596_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; 
lean_dec(v_h__1_596_);
v___x_600_ = lean_apply_2(v_h__2_597_, v_p_595_, lean_box(0));
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter(lean_object* v_motive_601_, lean_object* v_p_602_, lean_object* v_h__1_603_, lean_object* v_h__2_604_){
_start:
{
if (lean_obj_tag(v_p_602_) == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_h__2_604_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_apply_1(v_h__1_603_, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; 
lean_dec(v_h__1_603_);
v___x_607_ = lean_apply_2(v_h__2_604_, v_p_602_, lean_box(0));
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___redArg(lean_object* v_h_u2082_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_apply_1(v_h_u2082_608_, lean_box(0));
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset(lean_object* v_00_u03b1_610_, lean_object* v_a_611_, lean_object* v_b_612_, lean_object* v_k_613_, lean_object* v_h_u2081_614_, lean_object* v_h_u2082_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_apply_1(v_h_u2082_615_, lean_box(0));
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___boxed(lean_object* v_00_u03b1_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_k_620_, lean_object* v_h_u2081_621_, lean_object* v_h_u2082_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Nat_Internal_elimOffset(v_00_u03b1_617_, v_a_618_, v_b_619_, v_k_620_, v_h_u2081_621_, v_h_u2082_622_);
lean_dec(v_k_620_);
lean_dec(v_b_619_);
lean_dec(v_a_618_);
return v_res_623_;
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
