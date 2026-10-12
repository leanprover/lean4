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
uint8_t l_Nat_Internal_Linear_instBEqExpr_beq(lean_object* v_x_75_, lean_object* v_x_76_){
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
LEAN_EXPORT void l_Nat_Internal_Linear_instBEqExpr_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_75_ = stack[0].m_obj;
lean_object* v_x_76_ = stack[1].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_x_75_, v_x_76_);
stack->m_num = v_res_106_;
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqExpr_beq___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Nat_Internal_Linear_instBEqExpr_beq(v_x_107_, v_x_108_);
lean_dec_ref(v_x_108_);
lean_dec_ref(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_insert(lean_object* v_k_113_, lean_object* v_v_114_, lean_object* v_p_115_){
_start:
{
if (lean_obj_tag(v_p_115_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_k_113_);
lean_ctor_set(v___x_116_, 1, v_v_114_);
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_p_115_);
return v___x_117_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v_fst_120_; lean_object* v_snd_121_; uint8_t v___x_122_; 
v_head_118_ = lean_ctor_get(v_p_115_, 0);
lean_inc(v_head_118_);
v_tail_119_ = lean_ctor_get(v_p_115_, 1);
v_fst_120_ = lean_ctor_get(v_head_118_, 0);
v_snd_121_ = lean_ctor_get(v_head_118_, 1);
v___x_122_ = l_Nat_blt(v_v_114_, v_snd_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_144_; 
lean_inc(v_tail_119_);
v_isSharedCheck_144_ = !lean_is_exclusive(v_p_115_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_145_ = lean_ctor_get(v_p_115_, 1);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_p_115_, 0);
lean_dec(v_unused_146_);
v___x_124_ = v_p_115_;
v_isShared_125_ = v_isSharedCheck_144_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_p_115_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_144_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_eq(v_v_114_, v_snd_121_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = l_Nat_Internal_Linear_Poly_insert(v_k_113_, v_v_114_, v_tail_119_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_127_);
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_head_118_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_141_; 
lean_inc(v_snd_121_);
lean_inc(v_fst_120_);
lean_dec(v_v_114_);
v_isSharedCheck_141_ = !lean_is_exclusive(v_head_118_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; lean_object* v_unused_143_; 
v_unused_142_ = lean_ctor_get(v_head_118_, 1);
lean_dec(v_unused_142_);
v_unused_143_ = lean_ctor_get(v_head_118_, 0);
lean_dec(v_unused_143_);
v___x_132_ = v_head_118_;
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_head_118_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_nat_add(v_k_113_, v_fst_120_);
lean_dec(v_fst_120_);
lean_dec(v_k_113_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_snd_121_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_136_);
v___x_138_ = v___x_124_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_tail_119_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
else
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_isSharedCheck_154_ = !lean_is_exclusive(v_head_118_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_155_ = lean_ctor_get(v_head_118_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_head_118_, 0);
lean_dec(v_unused_156_);
v___x_148_ = v_head_118_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_dec(v_head_118_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_v_114_);
lean_ctor_set(v___x_148_, 0, v_k_113_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_k_113_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_v_114_);
v___x_151_ = v_reuseFailAlloc_153_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_p_115_);
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm_go(lean_object* v_p_157_, lean_object* v_r_158_){
_start:
{
if (lean_obj_tag(v_p_157_) == 0)
{
return v_r_158_;
}
else
{
lean_object* v_head_159_; lean_object* v_tail_160_; lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_163_; 
v_head_159_ = lean_ctor_get(v_p_157_, 0);
lean_inc(v_head_159_);
v_tail_160_ = lean_ctor_get(v_p_157_, 1);
lean_inc(v_tail_160_);
lean_dec_ref_known(v_p_157_, 2);
v_fst_161_ = lean_ctor_get(v_head_159_, 0);
lean_inc(v_fst_161_);
v_snd_162_ = lean_ctor_get(v_head_159_, 1);
lean_inc(v_snd_162_);
lean_dec(v_head_159_);
v___x_163_ = l_Nat_Internal_Linear_Poly_insert(v_fst_161_, v_snd_162_, v_r_158_);
v_p_157_ = v_tail_160_;
v_r_158_ = v___x_163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_norm(lean_object* v_p_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_Nat_Internal_Linear_Poly_norm_go(v_p_165_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancelAux(lean_object* v_fuel_168_, lean_object* v_m_u2081_169_, lean_object* v_m_u2082_170_, lean_object* v_r_u2081_171_, lean_object* v_r_u2082_172_){
_start:
{
lean_object* v_zero_173_; uint8_t v_isZero_174_; 
v_zero_173_ = lean_unsigned_to_nat(0u);
v_isZero_174_ = lean_nat_dec_eq(v_fuel_168_, v_zero_173_);
if (v_isZero_174_ == 1)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_fuel_168_);
v___x_175_ = l_List_reverse___redArg(v_r_u2081_171_);
v___x_176_ = l_List_appendTR___redArg(v___x_175_, v_m_u2081_169_);
v___x_177_ = l_List_reverse___redArg(v_r_u2082_172_);
v___x_178_ = l_List_appendTR___redArg(v___x_177_, v_m_u2082_170_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_176_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
else
{
if (lean_obj_tag(v_m_u2082_170_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_fuel_168_);
v___x_180_ = l_List_reverse___redArg(v_r_u2081_171_);
v___x_181_ = l_List_appendTR___redArg(v___x_180_, v_m_u2081_169_);
v___x_182_ = l_List_reverse___redArg(v_r_u2082_172_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
else
{
if (lean_obj_tag(v_m_u2081_169_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_fuel_168_);
v___x_184_ = l_List_reverse___redArg(v_r_u2081_171_);
v___x_185_ = l_List_reverse___redArg(v_r_u2082_172_);
v___x_186_ = l_List_appendTR___redArg(v___x_185_, v_m_u2082_170_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_184_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v_head_188_; lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v_tail_191_; lean_object* v_fst_192_; lean_object* v_snd_193_; lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v_one_196_; lean_object* v_n_197_; uint8_t v___x_198_; 
v_head_188_ = lean_ctor_get(v_m_u2081_169_, 0);
v_head_189_ = lean_ctor_get(v_m_u2082_170_, 0);
lean_inc(v_head_189_);
v_tail_190_ = lean_ctor_get(v_m_u2082_170_, 1);
v_tail_191_ = lean_ctor_get(v_m_u2081_169_, 1);
v_fst_192_ = lean_ctor_get(v_head_188_, 0);
v_snd_193_ = lean_ctor_get(v_head_188_, 1);
v_fst_194_ = lean_ctor_get(v_head_189_, 0);
v_snd_195_ = lean_ctor_get(v_head_189_, 1);
v_one_196_ = lean_unsigned_to_nat(1u);
v_n_197_ = lean_nat_sub(v_fuel_168_, v_one_196_);
lean_dec(v_fuel_168_);
v___x_198_ = l_Nat_blt(v_snd_193_, v_snd_195_);
if (v___x_198_ == 0)
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_238_; 
lean_inc(v_tail_190_);
v_isSharedCheck_238_ = !lean_is_exclusive(v_m_u2082_170_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; lean_object* v_unused_240_; 
v_unused_239_ = lean_ctor_get(v_m_u2082_170_, 1);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_m_u2082_170_, 0);
lean_dec(v_unused_240_);
v___x_200_ = v_m_u2082_170_;
v_isShared_201_ = v_isSharedCheck_238_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_m_u2082_170_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_238_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
uint8_t v___x_202_; 
v___x_202_ = l_Nat_blt(v_snd_195_, v_snd_193_);
if (v___x_202_ == 0)
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_231_; 
lean_inc(v_fst_194_);
lean_inc(v_snd_193_);
lean_inc(v_fst_192_);
lean_inc(v_tail_191_);
lean_del_object(v___x_200_);
v_isSharedCheck_231_ = !lean_is_exclusive(v_m_u2081_169_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_232_ = lean_ctor_get(v_m_u2081_169_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_m_u2081_169_, 0);
lean_dec(v_unused_233_);
v___x_204_ = v_m_u2081_169_;
v_isShared_205_ = v_isSharedCheck_231_;
goto v_resetjp_203_;
}
else
{
lean_dec(v_m_u2081_169_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_231_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_228_; 
v_isSharedCheck_228_ = !lean_is_exclusive(v_head_189_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; 
v_unused_229_ = lean_ctor_get(v_head_189_, 1);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_head_189_, 0);
lean_dec(v_unused_230_);
v___x_207_ = v_head_189_;
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_head_189_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v___x_209_; 
v___x_209_ = l_Nat_blt(v_fst_192_, v_fst_194_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = l_Nat_blt(v_fst_194_, v_fst_192_);
if (v___x_210_ == 0)
{
lean_del_object(v___x_207_);
lean_del_object(v___x_204_);
lean_dec(v_fst_194_);
lean_dec(v_snd_193_);
lean_dec(v_fst_192_);
v_fuel_168_ = v_n_197_;
v_m_u2081_169_ = v_tail_191_;
v_m_u2082_170_ = v_tail_190_;
goto _start;
}
else
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_nat_sub(v_fst_192_, v_fst_194_);
lean_dec(v_fst_194_);
lean_dec(v_fst_192_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_snd_193_);
lean_ctor_set(v___x_207_, 0, v___x_212_);
v___x_214_ = v___x_207_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_snd_193_);
v___x_214_ = v_reuseFailAlloc_219_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v_r_u2081_171_);
lean_ctor_set(v___x_204_, 0, v___x_214_);
v___x_216_ = v___x_204_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_r_u2081_171_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
v_fuel_168_ = v_n_197_;
v_m_u2081_169_ = v_tail_191_;
v_m_u2082_170_ = v_tail_190_;
v_r_u2081_171_ = v___x_216_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_nat_sub(v_fst_194_, v_fst_192_);
lean_dec(v_fst_192_);
lean_dec(v_fst_194_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_snd_193_);
lean_ctor_set(v___x_207_, 0, v___x_220_);
v___x_222_ = v___x_207_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_snd_193_);
v___x_222_ = v_reuseFailAlloc_227_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v_r_u2082_172_);
lean_ctor_set(v___x_204_, 0, v___x_222_);
v___x_224_ = v___x_204_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_r_u2082_172_);
v___x_224_ = v_reuseFailAlloc_226_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
v_fuel_168_ = v_n_197_;
v_m_u2081_169_ = v_tail_191_;
v_m_u2082_170_ = v_tail_190_;
v_r_u2082_172_ = v___x_224_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_235_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v_r_u2082_172_);
v___x_235_ = v___x_200_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_head_189_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_r_u2082_172_);
v___x_235_ = v_reuseFailAlloc_237_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v_fuel_168_ = v_n_197_;
v_m_u2082_170_ = v_tail_190_;
v_r_u2082_172_ = v___x_235_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
lean_inc(v_tail_191_);
lean_inc(v_head_188_);
lean_dec(v_head_189_);
v_isSharedCheck_248_ = !lean_is_exclusive(v_m_u2081_169_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; lean_object* v_unused_250_; 
v_unused_249_ = lean_ctor_get(v_m_u2081_169_, 1);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_m_u2081_169_, 0);
lean_dec(v_unused_250_);
v___x_242_ = v_m_u2081_169_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_m_u2081_169_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_r_u2081_171_);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_head_188_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_r_u2081_171_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v_fuel_168_ = v_n_197_;
v_m_u2081_169_ = v_tail_191_;
v_r_u2081_171_ = v___x_245_;
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
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(1000000u);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_cancel(lean_object* v_p_u2081_252_, lean_object* v_p_u2082_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(1000000u);
v___x_255_ = lean_box(0);
v___x_256_ = l_Nat_Internal_Linear_Poly_cancelAux(v___x_254_, v_p_u2081_252_, v_p_u2082_253_, v___x_255_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f(lean_object* v_p_259_){
_start:
{
if (lean_obj_tag(v_p_259_) == 0)
{
lean_object* v___x_260_; 
v___x_260_ = ((lean_object*)(l_Nat_Internal_Linear_Poly_isNum_x3f___closed__0));
return v___x_260_;
}
else
{
lean_object* v_tail_261_; 
v_tail_261_ = lean_ctor_get(v_p_259_, 1);
if (lean_obj_tag(v_tail_261_) == 0)
{
lean_object* v_head_262_; lean_object* v_fst_263_; lean_object* v_snd_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_head_262_ = lean_ctor_get(v_p_259_, 0);
v_fst_263_ = lean_ctor_get(v_head_262_, 0);
v_snd_264_ = lean_ctor_get(v_head_262_, 1);
v___x_265_ = lean_unsigned_to_nat(100000000u);
v___x_266_ = lean_nat_dec_eq(v_snd_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
lean_inc(v_fst_263_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_fst_263_);
return v___x_268_;
}
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(0);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNum_x3f___boxed(lean_object* v_p_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Nat_Internal_Linear_Poly_isNum_x3f(v_p_270_);
lean_dec(v_p_270_);
return v_res_271_;
}
}
uint8_t l_Nat_Internal_Linear_Poly_isZero(lean_object* v_p_272_){
_start:
{
if (lean_obj_tag(v_p_272_) == 0)
{
uint8_t v___x_273_; 
v___x_273_ = 1;
return v___x_273_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
}
LEAN_EXPORT void l_Nat_Internal_Linear_Poly_isZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_272_ = stack[0].m_obj;
uint8_t v_res_275_;
v_res_275_ = l_Nat_Internal_Linear_Poly_isZero(v_p_272_);
stack->m_num = v_res_275_;
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isZero___boxed(lean_object* v_p_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Nat_Internal_Linear_Poly_isZero(v_p_276_);
lean_dec(v_p_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
uint8_t l_Nat_Internal_Linear_Poly_isNonZero(lean_object* v_p_279_){
_start:
{
if (lean_obj_tag(v_p_279_) == 0)
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
else
{
lean_object* v_head_281_; lean_object* v_tail_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_head_281_ = lean_ctor_get(v_p_279_, 0);
v_tail_282_ = lean_ctor_get(v_p_279_, 1);
v_fst_283_ = lean_ctor_get(v_head_281_, 0);
v_snd_284_ = lean_ctor_get(v_head_281_, 1);
v___x_285_ = lean_unsigned_to_nat(100000000u);
v___x_286_ = lean_nat_dec_eq(v_snd_284_, v___x_285_);
if (v___x_286_ == 0)
{
v_p_279_ = v_tail_282_;
goto _start;
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_nat_dec_lt(v___x_288_, v_fst_283_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT void l_Nat_Internal_Linear_Poly_isNonZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_279_ = stack[0].m_obj;
uint8_t v_res_290_;
v_res_290_ = l_Nat_Internal_Linear_Poly_isNonZero(v_p_279_);
stack->m_num = v_res_290_;
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_isNonZero___boxed(lean_object* v_p_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Nat_Internal_Linear_Poly_isNonZero(v_p_291_);
lean_dec(v_p_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go(lean_object* v_coeff_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
switch(lean_obj_tag(v_a_295_))
{
case 0:
{
lean_object* v_v_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_v_297_ = lean_ctor_get(v_a_295_, 0);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v_v_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = lean_nat_mul(v_coeff_294_, v_v_297_);
lean_dec(v_coeff_294_);
v___x_301_ = lean_unsigned_to_nat(100000000u);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_296_);
return v___x_303_;
}
else
{
lean_dec(v_coeff_294_);
return v_a_296_;
}
}
case 1:
{
lean_object* v_i_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_i_304_ = lean_ctor_get(v_a_295_, 0);
lean_inc(v_i_304_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_coeff_294_);
lean_ctor_set(v___x_305_, 1, v_i_304_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_a_296_);
return v___x_306_;
}
case 2:
{
lean_object* v_a_307_; lean_object* v_b_308_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v_a_295_, 0);
v_b_308_ = lean_ctor_get(v_a_295_, 1);
lean_inc(v_coeff_294_);
v___x_309_ = l_Nat_Internal_Linear_Expr_toPoly_go(v_coeff_294_, v_b_308_, v_a_296_);
v_a_295_ = v_a_307_;
v_a_296_ = v___x_309_;
goto _start;
}
case 3:
{
lean_object* v_k_311_; lean_object* v_a_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_k_311_ = lean_ctor_get(v_a_295_, 0);
v_a_312_ = lean_ctor_get(v_a_295_, 1);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_nat_dec_eq(v_k_311_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_nat_mul(v_coeff_294_, v_k_311_);
lean_dec(v_coeff_294_);
v_coeff_294_ = v___x_315_;
v_a_295_ = v_a_312_;
goto _start;
}
else
{
lean_dec(v_coeff_294_);
return v_a_296_;
}
}
default: 
{
lean_object* v_a_317_; lean_object* v_k_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_a_317_ = lean_ctor_get(v_a_295_, 0);
v_k_318_ = lean_ctor_get(v_a_295_, 1);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_nat_dec_eq(v_k_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_nat_mul(v_coeff_294_, v_k_318_);
lean_dec(v_coeff_294_);
v_coeff_294_ = v___x_321_;
v_a_295_ = v_a_317_;
goto _start;
}
else
{
lean_dec(v_coeff_294_);
return v_a_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly_go___boxed(lean_object* v_coeff_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Nat_Internal_Linear_Expr_toPoly_go(v_coeff_323_, v_a_324_, v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly(lean_object* v_e_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_box(0);
v___x_330_ = l_Nat_Internal_Linear_Expr_toPoly_go(v___x_328_, v_e_327_, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toPoly___boxed(lean_object* v_e_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Nat_Internal_Linear_Expr_toPoly(v_e_331_);
lean_dec_ref(v_e_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly(lean_object* v_e_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = l_Nat_Internal_Linear_Expr_toPoly(v_e_333_);
v___x_335_ = l_Nat_Internal_Linear_Poly_norm(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_toNormPoly___boxed(lean_object* v_e_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_e_336_);
lean_dec_ref(v_e_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_inc(lean_object* v_e_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Nat_Internal_Linear_Expr_inc___closed__0));
v___x_342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_342_, 0, v_e_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
return v___x_342_;
}
}
uint8_t l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
if (lean_obj_tag(v_x_344_) == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 1;
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
else
{
if (lean_obj_tag(v_x_344_) == 0)
{
uint8_t v___x_347_; 
v___x_347_ = 0;
return v___x_347_;
}
else
{
lean_object* v_head_348_; lean_object* v_head_349_; lean_object* v_tail_350_; lean_object* v_tail_351_; lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; uint8_t v___x_356_; 
v_head_348_ = lean_ctor_get(v_x_343_, 0);
v_head_349_ = lean_ctor_get(v_x_344_, 0);
v_tail_350_ = lean_ctor_get(v_x_343_, 1);
v_tail_351_ = lean_ctor_get(v_x_344_, 1);
v_fst_352_ = lean_ctor_get(v_head_348_, 0);
v_snd_353_ = lean_ctor_get(v_head_348_, 1);
v_fst_354_ = lean_ctor_get(v_head_349_, 0);
v_snd_355_ = lean_ctor_get(v_head_349_, 1);
v___x_356_ = lean_nat_dec_eq(v_fst_352_, v_fst_354_);
if (v___x_356_ == 0)
{
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = lean_nat_dec_eq(v_snd_353_, v_snd_355_);
if (v___x_357_ == 0)
{
return v___x_357_;
}
else
{
v_x_343_ = v_tail_350_;
v_x_344_ = v_tail_351_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_343_ = stack[0].m_obj;
lean_object* v_x_344_ = stack[1].m_obj;
uint8_t v_res_359_;
v_res_359_ = l_List_beq___at___00Nat_Internal_Linear_instBEqPolyCnstr_beq_spec__0(v_x_343_, v_x_344_);
stack->m_num = v_res_359_;
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
uint8_t l_Nat_Internal_Linear_instBEqPolyCnstr_beq(lean_object* v_x_364_, lean_object* v_x_365_){
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
LEAN_EXPORT void l_Nat_Internal_Linear_instBEqPolyCnstr_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_364_ = stack[0].m_obj;
lean_object* v_x_365_ = stack[1].m_obj;
uint8_t v_res_375_;
v_res_375_ = l_Nat_Internal_Linear_instBEqPolyCnstr_beq(v_x_364_, v_x_365_);
stack->m_num = v_res_375_;
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_instBEqPolyCnstr_beq___boxed(lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Nat_Internal_Linear_instBEqPolyCnstr_beq(v_x_376_, v_x_377_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_norm(lean_object* v_c_382_){
_start:
{
uint8_t v_eq_383_; lean_object* v_lhs_384_; lean_object* v_rhs_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_397_; 
v_eq_383_ = lean_ctor_get_uint8(v_c_382_, sizeof(void*)*2);
v_lhs_384_ = lean_ctor_get(v_c_382_, 0);
v_rhs_385_ = lean_ctor_get(v_c_382_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_c_382_);
if (v_isSharedCheck_397_ == 0)
{
v___x_387_ = v_c_382_;
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_rhs_385_);
lean_inc(v_lhs_384_);
lean_dec(v_c_382_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_fst_392_; lean_object* v_snd_393_; lean_object* v___x_395_; 
v___x_389_ = l_Nat_Internal_Linear_Poly_norm(v_lhs_384_);
v___x_390_ = l_Nat_Internal_Linear_Poly_norm(v_rhs_385_);
v___x_391_ = l_Nat_Internal_Linear_Poly_cancel(v___x_389_, v___x_390_);
v_fst_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_fst_392_);
v_snd_393_ = lean_ctor_get(v___x_391_, 1);
lean_inc(v_snd_393_);
lean_dec_ref(v___x_391_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_snd_393_);
lean_ctor_set(v___x_387_, 0, v_fst_392_);
v___x_395_ = v___x_387_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_fst_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_snd_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_396_, sizeof(void*)*2, v_eq_383_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
uint8_t l_Nat_Internal_Linear_PolyCnstr_isUnsat(lean_object* v_c_398_){
_start:
{
uint8_t v_eq_399_; lean_object* v_lhs_400_; lean_object* v_rhs_401_; uint8_t v___y_403_; 
v_eq_399_ = lean_ctor_get_uint8(v_c_398_, sizeof(void*)*2);
v_lhs_400_ = lean_ctor_get(v_c_398_, 0);
v_rhs_401_ = lean_ctor_get(v_c_398_, 1);
if (v_eq_399_ == 0)
{
uint8_t v___x_406_; 
v___x_406_ = l_Nat_Internal_Linear_Poly_isNonZero(v_lhs_400_);
if (v___x_406_ == 0)
{
return v___x_406_;
}
else
{
uint8_t v___x_407_; 
v___x_407_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_401_);
return v___x_407_;
}
}
else
{
uint8_t v___x_408_; 
v___x_408_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_400_);
if (v___x_408_ == 0)
{
v___y_403_ = v___x_408_;
goto v___jp_402_;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = l_Nat_Internal_Linear_Poly_isNonZero(v_rhs_401_);
v___y_403_ = v___x_409_;
goto v___jp_402_;
}
}
v___jp_402_:
{
if (v___y_403_ == 0)
{
uint8_t v___x_404_; 
v___x_404_ = l_Nat_Internal_Linear_Poly_isNonZero(v_lhs_400_);
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
uint8_t v___x_405_; 
v___x_405_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_401_);
return v___x_405_;
}
}
else
{
return v___y_403_;
}
}
}
}
LEAN_EXPORT void l_Nat_Internal_Linear_PolyCnstr_isUnsat_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_398_ = stack[0].m_obj;
uint8_t v_res_410_;
v_res_410_ = l_Nat_Internal_Linear_PolyCnstr_isUnsat(v_c_398_);
stack->m_num = v_res_410_;
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isUnsat___boxed(lean_object* v_c_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Nat_Internal_Linear_PolyCnstr_isUnsat(v_c_411_);
lean_dec_ref(v_c_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
uint8_t l_Nat_Internal_Linear_PolyCnstr_isValid(lean_object* v_c_414_){
_start:
{
uint8_t v_eq_415_; 
v_eq_415_ = lean_ctor_get_uint8(v_c_414_, sizeof(void*)*2);
if (v_eq_415_ == 0)
{
lean_object* v_lhs_416_; uint8_t v___x_417_; 
v_lhs_416_ = lean_ctor_get(v_c_414_, 0);
v___x_417_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_416_);
return v___x_417_;
}
else
{
lean_object* v_lhs_418_; lean_object* v_rhs_419_; uint8_t v___x_420_; 
v_lhs_418_ = lean_ctor_get(v_c_414_, 0);
v_rhs_419_ = lean_ctor_get(v_c_414_, 1);
v___x_420_ = l_Nat_Internal_Linear_Poly_isZero(v_lhs_418_);
if (v___x_420_ == 0)
{
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = l_Nat_Internal_Linear_Poly_isZero(v_rhs_419_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT void l_Nat_Internal_Linear_PolyCnstr_isValid_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_414_ = stack[0].m_obj;
uint8_t v_res_422_;
v_res_422_ = l_Nat_Internal_Linear_PolyCnstr_isValid(v_c_414_);
stack->m_num = v_res_422_;
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_isValid___boxed(lean_object* v_c_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Nat_Internal_Linear_PolyCnstr_isValid(v_c_423_);
lean_dec_ref(v_c_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toPoly(lean_object* v_c_426_){
_start:
{
uint8_t v_eq_427_; lean_object* v_lhs_428_; lean_object* v_rhs_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_438_; 
v_eq_427_ = lean_ctor_get_uint8(v_c_426_, sizeof(void*)*2);
v_lhs_428_ = lean_ctor_get(v_c_426_, 0);
v_rhs_429_ = lean_ctor_get(v_c_426_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_c_426_);
if (v_isSharedCheck_438_ == 0)
{
v___x_431_ = v_c_426_;
v_isShared_432_ = v_isSharedCheck_438_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_rhs_429_);
lean_inc(v_lhs_428_);
lean_dec(v_c_426_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_438_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_433_ = l_Nat_Internal_Linear_Expr_toPoly(v_lhs_428_);
lean_dec_ref(v_lhs_428_);
v___x_434_ = l_Nat_Internal_Linear_Expr_toPoly(v_rhs_429_);
lean_dec_ref(v_rhs_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_434_);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*2, v_eq_427_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_toNormPoly(lean_object* v_c_439_){
_start:
{
uint8_t v_eq_440_; lean_object* v_lhs_441_; lean_object* v_rhs_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_eq_440_ = lean_ctor_get_uint8(v_c_439_, sizeof(void*)*2);
v_lhs_441_ = lean_ctor_get(v_c_439_, 0);
v_rhs_442_ = lean_ctor_get(v_c_439_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_c_439_);
if (v_isSharedCheck_454_ == 0)
{
v___x_444_ = v_c_439_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_rhs_442_);
lean_inc(v_lhs_441_);
lean_dec(v_c_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; 
v___x_446_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_lhs_441_);
lean_dec_ref(v_lhs_441_);
v___x_447_ = l_Nat_Internal_Linear_Expr_toNormPoly(v_rhs_442_);
lean_dec_ref(v_rhs_442_);
v___x_448_ = l_Nat_Internal_Linear_Poly_cancel(v___x_446_, v___x_447_);
v_fst_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_fst_449_);
v_snd_450_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_snd_450_);
lean_dec_ref(v___x_448_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_snd_450_);
lean_ctor_set(v___x_444_, 0, v_fst_449_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_snd_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*2, v_eq_440_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_monomialToExpr(lean_object* v_k_455_, lean_object* v_v_456_){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(100000000u);
v___x_458_ = lean_nat_dec_eq(v_v_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_dec_eq(v_k_455_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_v_456_);
v___x_462_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_462_, 0, v_k_455_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v_k_455_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_v_456_);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_v_456_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_k_455_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr_go(lean_object* v_e_465_, lean_object* v_p_466_){
_start:
{
if (lean_obj_tag(v_p_466_) == 0)
{
return v_e_465_;
}
else
{
lean_object* v_head_467_; lean_object* v_tail_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_head_467_ = lean_ctor_get(v_p_466_, 0);
lean_inc(v_head_467_);
v_tail_468_ = lean_ctor_get(v_p_466_, 1);
lean_inc(v_tail_468_);
lean_dec_ref_known(v_p_466_, 2);
v_fst_469_ = lean_ctor_get(v_head_467_, 0);
v_snd_470_ = lean_ctor_get(v_head_467_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_head_467_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v_head_467_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snd_470_);
lean_inc(v_fst_469_);
lean_dec(v_head_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = l_Nat_Internal_Linear_monomialToExpr(v_fst_469_, v_snd_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 2);
lean_ctor_set(v___x_472_, 1, v___x_474_);
lean_ctor_set(v___x_472_, 0, v_e_465_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_e_465_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_478_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
v_e_465_ = v___x_476_;
v_p_466_ = v_tail_468_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Poly_toExpr(lean_object* v_p_480_){
_start:
{
if (lean_obj_tag(v_p_480_) == 0)
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l_Nat_Internal_Linear_instInhabitedExpr_default___closed__0));
return v___x_481_;
}
else
{
lean_object* v_head_482_; lean_object* v_tail_483_; lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_head_482_ = lean_ctor_get(v_p_480_, 0);
lean_inc(v_head_482_);
v_tail_483_ = lean_ctor_get(v_p_480_, 1);
lean_inc(v_tail_483_);
lean_dec_ref_known(v_p_480_, 2);
v_fst_484_ = lean_ctor_get(v_head_482_, 0);
lean_inc(v_fst_484_);
v_snd_485_ = lean_ctor_get(v_head_482_, 1);
lean_inc(v_snd_485_);
lean_dec(v_head_482_);
v___x_486_ = l_Nat_Internal_Linear_monomialToExpr(v_fst_484_, v_snd_485_);
v___x_487_ = l_Nat_Internal_Linear_Poly_toExpr_go(v___x_486_, v_tail_483_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_PolyCnstr_toExpr(lean_object* v_c_488_){
_start:
{
uint8_t v_eq_489_; lean_object* v_lhs_490_; lean_object* v_rhs_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
v_eq_489_ = lean_ctor_get_uint8(v_c_488_, sizeof(void*)*2);
v_lhs_490_ = lean_ctor_get(v_c_488_, 0);
v_rhs_491_ = lean_ctor_get(v_c_488_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_c_488_);
if (v_isSharedCheck_500_ == 0)
{
v___x_493_ = v_c_488_;
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_rhs_491_);
lean_inc(v_lhs_490_);
lean_dec(v_c_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = l_Nat_Internal_Linear_Poly_toExpr(v_lhs_490_);
v___x_496_ = l_Nat_Internal_Linear_Poly_toExpr(v_rhs_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_496_);
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_498_ = v___x_493_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*2, v_eq_489_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object* v_fuel_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
lean_object* v_zero_504_; uint8_t v_isZero_505_; 
v_zero_504_ = lean_unsigned_to_nat(0u);
v_isZero_505_ = lean_nat_dec_eq(v_fuel_501_, v_zero_504_);
if (v_isZero_505_ == 1)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_h__2_503_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_apply_1(v_h__1_502_, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v_one_508_; lean_object* v_n_509_; lean_object* v___x_510_; 
lean_dec(v_h__1_502_);
v_one_508_ = lean_unsigned_to_nat(1u);
v_n_509_ = lean_nat_sub(v_fuel_501_, v_one_508_);
v___x_510_ = lean_apply_1(v_h__2_503_, v_n_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object* v_fuel_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___redArg(v_fuel_511_, v_h__1_512_, v_h__2_513_);
lean_dec(v_fuel_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(lean_object* v_motive_515_, lean_object* v_fuel_516_, lean_object* v_h__1_517_, lean_object* v_h__2_518_){
_start:
{
lean_object* v_zero_519_; uint8_t v_isZero_520_; 
v_zero_519_ = lean_unsigned_to_nat(0u);
v_isZero_520_ = lean_nat_dec_eq(v_fuel_516_, v_zero_519_);
if (v_isZero_520_ == 1)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_h__2_518_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_apply_1(v_h__1_517_, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_one_523_; lean_object* v_n_524_; lean_object* v___x_525_; 
lean_dec(v_h__1_517_);
v_one_523_ = lean_unsigned_to_nat(1u);
v_n_524_ = lean_nat_sub(v_fuel_516_, v_one_523_);
v___x_525_ = lean_apply_1(v_h__2_518_, v_n_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object* v_motive_526_, lean_object* v_fuel_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__3_splitter(v_motive_526_, v_fuel_527_, v_h__1_528_, v_h__2_529_);
lean_dec(v_fuel_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object* v_m_u2081_531_, lean_object* v_m_u2082_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_, lean_object* v_h__3_535_){
_start:
{
if (lean_obj_tag(v_m_u2082_532_) == 0)
{
lean_object* v___x_536_; 
lean_dec(v_h__3_535_);
lean_dec(v_h__2_534_);
v___x_536_ = lean_apply_1(v_h__1_533_, v_m_u2081_531_);
return v___x_536_;
}
else
{
lean_dec(v_h__1_533_);
if (lean_obj_tag(v_m_u2081_531_) == 0)
{
lean_object* v___x_537_; 
lean_dec(v_h__3_535_);
v___x_537_ = lean_apply_2(v_h__2_534_, v_m_u2082_532_, lean_box(0));
return v___x_537_;
}
else
{
lean_object* v_head_538_; lean_object* v_head_539_; lean_object* v_tail_540_; lean_object* v_tail_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_546_; 
lean_dec(v_h__2_534_);
v_head_538_ = lean_ctor_get(v_m_u2081_531_, 0);
lean_inc(v_head_538_);
v_head_539_ = lean_ctor_get(v_m_u2082_532_, 0);
lean_inc(v_head_539_);
v_tail_540_ = lean_ctor_get(v_m_u2082_532_, 1);
lean_inc(v_tail_540_);
lean_dec_ref_known(v_m_u2082_532_, 2);
v_tail_541_ = lean_ctor_get(v_m_u2081_531_, 1);
lean_inc(v_tail_541_);
lean_dec_ref_known(v_m_u2081_531_, 2);
v_fst_542_ = lean_ctor_get(v_head_538_, 0);
lean_inc(v_fst_542_);
v_snd_543_ = lean_ctor_get(v_head_538_, 1);
lean_inc(v_snd_543_);
lean_dec(v_head_538_);
v_fst_544_ = lean_ctor_get(v_head_539_, 0);
lean_inc(v_fst_544_);
v_snd_545_ = lean_ctor_get(v_head_539_, 1);
lean_inc(v_snd_545_);
lean_dec(v_head_539_);
v___x_546_ = lean_apply_6(v_h__3_535_, v_fst_542_, v_snd_543_, v_tail_541_, v_fst_544_, v_snd_545_, v_tail_540_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_cancelAux_match__1_splitter(lean_object* v_motive_547_, lean_object* v_m_u2081_548_, lean_object* v_m_u2082_549_, lean_object* v_h__1_550_, lean_object* v_h__2_551_, lean_object* v_h__3_552_){
_start:
{
if (lean_obj_tag(v_m_u2082_549_) == 0)
{
lean_object* v___x_553_; 
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
v___x_553_ = lean_apply_1(v_h__1_550_, v_m_u2081_548_);
return v___x_553_;
}
else
{
lean_dec(v_h__1_550_);
if (lean_obj_tag(v_m_u2081_548_) == 0)
{
lean_object* v___x_554_; 
lean_dec(v_h__3_552_);
v___x_554_ = lean_apply_2(v_h__2_551_, v_m_u2082_549_, lean_box(0));
return v___x_554_;
}
else
{
lean_object* v_head_555_; lean_object* v_head_556_; lean_object* v_tail_557_; lean_object* v_tail_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_551_);
v_head_555_ = lean_ctor_get(v_m_u2081_548_, 0);
lean_inc(v_head_555_);
v_head_556_ = lean_ctor_get(v_m_u2082_549_, 0);
lean_inc(v_head_556_);
v_tail_557_ = lean_ctor_get(v_m_u2082_549_, 1);
lean_inc(v_tail_557_);
lean_dec_ref_known(v_m_u2082_549_, 2);
v_tail_558_ = lean_ctor_get(v_m_u2081_548_, 1);
lean_inc(v_tail_558_);
lean_dec_ref_known(v_m_u2081_548_, 2);
v_fst_559_ = lean_ctor_get(v_head_555_, 0);
lean_inc(v_fst_559_);
v_snd_560_ = lean_ctor_get(v_head_555_, 1);
lean_inc(v_snd_560_);
lean_dec(v_head_555_);
v_fst_561_ = lean_ctor_get(v_head_556_, 0);
lean_inc(v_fst_561_);
v_snd_562_ = lean_ctor_get(v_head_556_, 1);
lean_inc(v_snd_562_);
lean_dec(v_head_556_);
v___x_563_ = lean_apply_6(v_h__3_552_, v_fst_559_, v_snd_560_, v_tail_558_, v_fst_561_, v_snd_562_, v_tail_557_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object* v_x_564_, lean_object* v_h__1_565_, lean_object* v_h__2_566_, lean_object* v_h__3_567_, lean_object* v_h__4_568_, lean_object* v_h__5_569_){
_start:
{
switch(lean_obj_tag(v_x_564_))
{
case 0:
{
lean_object* v_v_570_; lean_object* v___x_571_; 
lean_dec(v_h__5_569_);
lean_dec(v_h__4_568_);
lean_dec(v_h__3_567_);
lean_dec(v_h__2_566_);
v_v_570_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_v_570_);
lean_dec_ref_known(v_x_564_, 1);
v___x_571_ = lean_apply_1(v_h__1_565_, v_v_570_);
return v___x_571_;
}
case 1:
{
lean_object* v_i_572_; lean_object* v___x_573_; 
lean_dec(v_h__5_569_);
lean_dec(v_h__4_568_);
lean_dec(v_h__3_567_);
lean_dec(v_h__1_565_);
v_i_572_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_i_572_);
lean_dec_ref_known(v_x_564_, 1);
v___x_573_ = lean_apply_1(v_h__2_566_, v_i_572_);
return v___x_573_;
}
case 2:
{
lean_object* v_a_574_; lean_object* v_b_575_; lean_object* v___x_576_; 
lean_dec(v_h__5_569_);
lean_dec(v_h__4_568_);
lean_dec(v_h__2_566_);
lean_dec(v_h__1_565_);
v_a_574_ = lean_ctor_get(v_x_564_, 0);
lean_inc_ref(v_a_574_);
v_b_575_ = lean_ctor_get(v_x_564_, 1);
lean_inc_ref(v_b_575_);
lean_dec_ref_known(v_x_564_, 2);
v___x_576_ = lean_apply_2(v_h__3_567_, v_a_574_, v_b_575_);
return v___x_576_;
}
case 3:
{
lean_object* v_k_577_; lean_object* v_a_578_; lean_object* v___x_579_; 
lean_dec(v_h__5_569_);
lean_dec(v_h__3_567_);
lean_dec(v_h__2_566_);
lean_dec(v_h__1_565_);
v_k_577_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_k_577_);
v_a_578_ = lean_ctor_get(v_x_564_, 1);
lean_inc_ref(v_a_578_);
lean_dec_ref_known(v_x_564_, 2);
v___x_579_ = lean_apply_2(v_h__4_568_, v_k_577_, v_a_578_);
return v___x_579_;
}
default: 
{
lean_object* v_a_580_; lean_object* v_k_581_; lean_object* v___x_582_; 
lean_dec(v_h__4_568_);
lean_dec(v_h__3_567_);
lean_dec(v_h__2_566_);
lean_dec(v_h__1_565_);
v_a_580_ = lean_ctor_get(v_x_564_, 0);
lean_inc_ref(v_a_580_);
v_k_581_ = lean_ctor_get(v_x_564_, 1);
lean_inc(v_k_581_);
lean_dec_ref_known(v_x_564_, 2);
v___x_582_ = lean_apply_2(v_h__5_569_, v_a_580_, v_k_581_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Expr_toPoly_go_match__1_splitter(lean_object* v_motive_583_, lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_, lean_object* v_h__3_587_, lean_object* v_h__4_588_, lean_object* v_h__5_589_){
_start:
{
switch(lean_obj_tag(v_x_584_))
{
case 0:
{
lean_object* v_v_590_; lean_object* v___x_591_; 
lean_dec(v_h__5_589_);
lean_dec(v_h__4_588_);
lean_dec(v_h__3_587_);
lean_dec(v_h__2_586_);
v_v_590_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_v_590_);
lean_dec_ref_known(v_x_584_, 1);
v___x_591_ = lean_apply_1(v_h__1_585_, v_v_590_);
return v___x_591_;
}
case 1:
{
lean_object* v_i_592_; lean_object* v___x_593_; 
lean_dec(v_h__5_589_);
lean_dec(v_h__4_588_);
lean_dec(v_h__3_587_);
lean_dec(v_h__1_585_);
v_i_592_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_i_592_);
lean_dec_ref_known(v_x_584_, 1);
v___x_593_ = lean_apply_1(v_h__2_586_, v_i_592_);
return v___x_593_;
}
case 2:
{
lean_object* v_a_594_; lean_object* v_b_595_; lean_object* v___x_596_; 
lean_dec(v_h__5_589_);
lean_dec(v_h__4_588_);
lean_dec(v_h__2_586_);
lean_dec(v_h__1_585_);
v_a_594_ = lean_ctor_get(v_x_584_, 0);
lean_inc_ref(v_a_594_);
v_b_595_ = lean_ctor_get(v_x_584_, 1);
lean_inc_ref(v_b_595_);
lean_dec_ref_known(v_x_584_, 2);
v___x_596_ = lean_apply_2(v_h__3_587_, v_a_594_, v_b_595_);
return v___x_596_;
}
case 3:
{
lean_object* v_k_597_; lean_object* v_a_598_; lean_object* v___x_599_; 
lean_dec(v_h__5_589_);
lean_dec(v_h__3_587_);
lean_dec(v_h__2_586_);
lean_dec(v_h__1_585_);
v_k_597_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_k_597_);
v_a_598_ = lean_ctor_get(v_x_584_, 1);
lean_inc_ref(v_a_598_);
lean_dec_ref_known(v_x_584_, 2);
v___x_599_ = lean_apply_2(v_h__4_588_, v_k_597_, v_a_598_);
return v___x_599_;
}
default: 
{
lean_object* v_a_600_; lean_object* v_k_601_; lean_object* v___x_602_; 
lean_dec(v_h__4_588_);
lean_dec(v_h__3_587_);
lean_dec(v_h__2_586_);
lean_dec(v_h__1_585_);
v_a_600_ = lean_ctor_get(v_x_584_, 0);
lean_inc_ref(v_a_600_);
v_k_601_ = lean_ctor_get(v_x_584_, 1);
lean_inc(v_k_601_);
lean_dec_ref_known(v_x_584_, 2);
v___x_602_ = lean_apply_2(v_h__5_589_, v_a_600_, v_k_601_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter___redArg(lean_object* v_p_603_, lean_object* v_h__1_604_, lean_object* v_h__2_605_){
_start:
{
if (lean_obj_tag(v_p_603_) == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v_h__2_605_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_apply_1(v_h__1_604_, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; 
lean_dec(v_h__1_604_);
v___x_608_ = lean_apply_2(v_h__2_605_, v_p_603_, lean_box(0));
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_Linear_0__Nat_Internal_Linear_Poly_isZero_match__1_splitter(lean_object* v_motive_609_, lean_object* v_p_610_, lean_object* v_h__1_611_, lean_object* v_h__2_612_){
_start:
{
if (lean_obj_tag(v_p_610_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_h__2_612_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_apply_1(v_h__1_611_, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
lean_dec(v_h__1_611_);
v___x_615_ = lean_apply_2(v_h__2_612_, v_p_610_, lean_box(0));
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___redArg(lean_object* v_h_u2082_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_apply_1(v_h_u2082_616_, lean_box(0));
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset(lean_object* v_00_u03b1_618_, lean_object* v_a_619_, lean_object* v_b_620_, lean_object* v_k_621_, lean_object* v_h_u2081_622_, lean_object* v_h_u2082_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_apply_1(v_h_u2082_623_, lean_box(0));
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_elimOffset___boxed(lean_object* v_00_u03b1_625_, lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_k_628_, lean_object* v_h_u2081_629_, lean_object* v_h_u2082_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Nat_Internal_elimOffset(v_00_u03b1_625_, v_a_626_, v_b_627_, v_k_628_, v_h_u2081_629_, v_h_u2082_630_);
lean_dec(v_k_628_);
lean_dec(v_b_627_);
lean_dec(v_a_626_);
return v_res_631_;
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
