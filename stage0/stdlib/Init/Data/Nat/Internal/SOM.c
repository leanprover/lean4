// Lean compiler output
// Module: Init.Data.Nat.Internal.SOM
// Imports: public import Init.Data.Nat.Internal.Linear import Init.ByCases import Init.Data.List.BasicAux import Init.Data.Prod import Init.Meta
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
uint8_t l_List_decidableLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_Internal_SOM_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_Internal_SOM_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Nat_Internal_SOM_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Internal_SOM_instInhabitedExpr_default = (const lean_object*)&l_Nat_Internal_SOM_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_Internal_SOM_instInhabitedExpr = (const lean_object*)&l_Nat_Internal_SOM_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Mon_mul(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_insertSorted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mulMon_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Nat_Internal_SOM_Expr_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 2:
{
lean_object* v_a_7_; lean_object* v_b_8_; lean_object* v___x_9_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_7_);
v_b_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_a_7_, v_b_8_);
return v___x_9_;
}
case 3:
{
lean_object* v_a_10_; lean_object* v_b_11_; lean_object* v___x_12_; 
v_a_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_10_);
v_b_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_11_);
lean_dec_ref_known(v_t_5_, 2);
v___x_12_ = lean_apply_2(v_k_6_, v_a_10_, v_b_11_);
return v___x_12_;
}
default: 
{
lean_object* v_i_13_; lean_object* v___x_14_; 
v_i_13_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_i_13_);
lean_dec_ref(v_t_5_);
v___x_14_ = lean_apply_1(v_k_6_, v_i_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Nat_Internal_SOM_Expr_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_num_elim___redArg(lean_object* v_t_27_, lean_object* v_num_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_27_, v_num_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_num_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_num_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_31_, v_num_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_var_elim___redArg(lean_object* v_t_35_, lean_object* v_var_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_35_, v_var_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_var_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_var_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_39_, v_var_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_add_elim___redArg(lean_object* v_t_43_, lean_object* v_add_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_43_, v_add_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_add_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_add_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_47_, v_add_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_mul_elim___redArg(lean_object* v_t_51_, lean_object* v_mul_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_51_, v_mul_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_mul_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_mul_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Nat_Internal_SOM_Expr_ctorElim___redArg(v_t_55_, v_mul_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(lean_object* v_fuel_63_, lean_object* v_m_u2081_64_, lean_object* v_m_u2082_65_){
_start:
{
lean_object* v_zero_66_; uint8_t v_isZero_67_; 
v_zero_66_ = lean_unsigned_to_nat(0u);
v_isZero_67_ = lean_nat_dec_eq(v_fuel_63_, v_zero_66_);
if (v_isZero_67_ == 1)
{
lean_object* v___x_68_; 
v___x_68_ = l_List_appendTR___redArg(v_m_u2081_64_, v_m_u2082_65_);
return v___x_68_;
}
else
{
if (lean_obj_tag(v_m_u2082_65_) == 0)
{
return v_m_u2081_64_;
}
else
{
if (lean_obj_tag(v_m_u2081_64_) == 0)
{
return v_m_u2082_65_;
}
else
{
lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v_one_73_; lean_object* v_n_74_; uint8_t v___x_75_; 
v_head_69_ = lean_ctor_get(v_m_u2082_65_, 0);
v_tail_70_ = lean_ctor_get(v_m_u2082_65_, 1);
v_head_71_ = lean_ctor_get(v_m_u2081_64_, 0);
v_tail_72_ = lean_ctor_get(v_m_u2081_64_, 1);
v_one_73_ = lean_unsigned_to_nat(1u);
v_n_74_ = lean_nat_sub(v_fuel_63_, v_one_73_);
v___x_75_ = l_Nat_blt(v_head_71_, v_head_69_);
if (v___x_75_ == 0)
{
lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_97_; 
lean_inc(v_tail_70_);
lean_inc(v_head_69_);
v_isSharedCheck_97_ = !lean_is_exclusive(v_m_u2082_65_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; lean_object* v_unused_99_; 
v_unused_98_ = lean_ctor_get(v_m_u2082_65_, 1);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_m_u2082_65_, 0);
lean_dec(v_unused_99_);
v___x_77_ = v_m_u2082_65_;
v_isShared_78_ = v_isSharedCheck_97_;
goto v_resetjp_76_;
}
else
{
lean_dec(v_m_u2082_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_97_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; 
v___x_79_ = l_Nat_blt(v_head_69_, v_head_71_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_90_; 
lean_inc(v_tail_72_);
lean_inc(v_head_71_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_m_u2081_64_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; 
v_unused_91_ = lean_ctor_get(v_m_u2081_64_, 1);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_m_u2081_64_, 0);
lean_dec(v_unused_92_);
v___x_81_ = v_m_u2081_64_;
v_isShared_82_ = v_isSharedCheck_90_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_u2081_64_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_90_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(v_n_74_, v_tail_72_, v_tail_70_);
lean_dec(v_n_74_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_83_);
lean_ctor_set(v___x_81_, 0, v_head_69_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_head_69_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_83_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_85_);
lean_ctor_set(v___x_77_, 0, v_head_71_);
v___x_87_ = v___x_77_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_head_71_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(v_n_74_, v_m_u2081_64_, v_tail_70_);
lean_dec(v_n_74_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_93_);
v___x_95_ = v___x_77_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_head_69_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
lean_inc(v_tail_72_);
lean_inc(v_head_71_);
v_isSharedCheck_107_ = !lean_is_exclusive(v_m_u2081_64_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; 
v_unused_108_ = lean_ctor_get(v_m_u2081_64_, 1);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_m_u2081_64_, 0);
lean_dec(v_unused_109_);
v___x_101_ = v_m_u2081_64_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_m_u2081_64_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(v_n_74_, v_tail_72_, v_m_u2082_65_);
lean_dec(v_n_74_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_head_71_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go___boxed(lean_object* v_fuel_110_, lean_object* v_m_u2081_111_, lean_object* v_m_u2082_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(v_fuel_110_, v_m_u2081_111_, v_m_u2082_112_);
lean_dec(v_fuel_110_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Mon_mul(lean_object* v_m_u2081_114_, lean_object* v_m_u2082_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1000000u);
v___x_117_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go(v___x_116_, v_m_u2081_114_, v_m_u2082_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go(lean_object* v_fuel_119_, lean_object* v_p_u2081_120_, lean_object* v_p_u2082_121_){
_start:
{
lean_object* v_zero_122_; uint8_t v_isZero_123_; 
v_zero_122_ = lean_unsigned_to_nat(0u);
v_isZero_123_ = lean_nat_dec_eq(v_fuel_119_, v_zero_122_);
if (v_isZero_123_ == 1)
{
lean_object* v___x_124_; 
lean_dec(v_fuel_119_);
v___x_124_ = l_List_appendTR___redArg(v_p_u2081_120_, v_p_u2082_121_);
return v___x_124_;
}
else
{
if (lean_obj_tag(v_p_u2082_121_) == 0)
{
lean_dec(v_fuel_119_);
return v_p_u2081_120_;
}
else
{
if (lean_obj_tag(v_p_u2081_120_) == 0)
{
lean_dec(v_fuel_119_);
return v_p_u2082_121_;
}
else
{
lean_object* v_head_125_; lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v_tail_128_; lean_object* v_fst_129_; lean_object* v_snd_130_; lean_object* v_fst_131_; lean_object* v_snd_132_; lean_object* v_one_133_; lean_object* v_n_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_head_125_ = lean_ctor_get(v_p_u2081_120_, 0);
v_head_126_ = lean_ctor_get(v_p_u2082_121_, 0);
lean_inc(v_head_126_);
v_tail_127_ = lean_ctor_get(v_p_u2082_121_, 1);
v_tail_128_ = lean_ctor_get(v_p_u2081_120_, 1);
v_fst_129_ = lean_ctor_get(v_head_125_, 0);
v_snd_130_ = lean_ctor_get(v_head_125_, 1);
v_fst_131_ = lean_ctor_get(v_head_126_, 0);
v_snd_132_ = lean_ctor_get(v_head_126_, 1);
v_one_133_ = lean_unsigned_to_nat(1u);
v_n_134_ = lean_nat_sub(v_fuel_119_, v_one_133_);
lean_dec(v_fuel_119_);
v___x_135_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_136_ = ((lean_object*)(l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go___closed__0));
lean_inc(v_snd_132_);
lean_inc(v_snd_130_);
lean_inc_ref(v___x_135_);
v___x_137_ = l_List_decidableLex___redArg(v___x_135_, v___x_136_, v_snd_130_, v_snd_132_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_168_; 
lean_inc(v_tail_127_);
v_isSharedCheck_168_ = !lean_is_exclusive(v_p_u2082_121_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; lean_object* v_unused_170_; 
v_unused_169_ = lean_ctor_get(v_p_u2082_121_, 1);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_p_u2082_121_, 0);
lean_dec(v_unused_170_);
v___x_139_ = v_p_u2082_121_;
v_isShared_140_ = v_isSharedCheck_168_;
goto v_resetjp_138_;
}
else
{
lean_dec(v_p_u2082_121_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_168_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint8_t v___x_141_; 
lean_inc(v_snd_130_);
lean_inc(v_snd_132_);
v___x_141_ = l_List_decidableLex___redArg(v___x_135_, v___x_136_, v_snd_132_, v_snd_130_);
if (v___x_141_ == 0)
{
lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_161_; 
lean_inc(v_fst_131_);
lean_inc(v_snd_130_);
lean_inc(v_fst_129_);
lean_inc(v_tail_128_);
lean_del_object(v___x_139_);
v_isSharedCheck_161_ = !lean_is_exclusive(v_p_u2081_120_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; 
v_unused_162_ = lean_ctor_get(v_p_u2081_120_, 1);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_p_u2081_120_, 0);
lean_dec(v_unused_163_);
v___x_143_ = v_p_u2081_120_;
v_isShared_144_ = v_isSharedCheck_161_;
goto v_resetjp_142_;
}
else
{
lean_dec(v_p_u2081_120_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_161_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_158_; 
v_isSharedCheck_158_ = !lean_is_exclusive(v_head_126_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_159_ = lean_ctor_get(v_head_126_, 1);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_head_126_, 0);
lean_dec(v_unused_160_);
v___x_146_ = v_head_126_;
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
else
{
lean_dec(v_head_126_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_nat_add(v_fst_129_, v_fst_131_);
lean_dec(v_fst_131_);
lean_dec(v_fst_129_);
v___x_149_ = lean_nat_dec_eq(v___x_148_, v_zero_122_);
if (v___x_149_ == 0)
{
lean_object* v___x_151_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v_snd_130_);
lean_ctor_set(v___x_146_, 0, v___x_148_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_snd_130_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go(v_n_134_, v_tail_128_, v_tail_127_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_152_);
lean_ctor_set(v___x_143_, 0, v___x_151_);
v___x_154_ = v___x_143_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_dec(v___x_148_);
lean_del_object(v___x_146_);
lean_del_object(v___x_143_);
lean_dec(v_snd_130_);
v_fuel_119_ = v_n_134_;
v_p_u2081_120_ = v_tail_128_;
v_p_u2082_121_ = v_tail_127_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go(v_n_134_, v_p_u2081_120_, v_tail_127_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_164_);
v___x_166_ = v___x_139_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_head_126_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
lean_inc(v_tail_128_);
lean_inc(v_head_125_);
lean_dec_ref(v___x_135_);
lean_dec(v_head_126_);
v_isSharedCheck_178_ = !lean_is_exclusive(v_p_u2081_120_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_179_ = lean_ctor_get(v_p_u2081_120_, 1);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_p_u2081_120_, 0);
lean_dec(v_unused_180_);
v___x_172_ = v_p_u2081_120_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_dec(v_p_u2081_120_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go(v_n_134_, v_tail_128_, v_p_u2082_121_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_174_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_head_125_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_add(lean_object* v_p_u2081_181_, lean_object* v_p_u2082_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1000000u);
v___x_184_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go(v___x_183_, v_p_u2081_181_, v_p_u2082_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_insertSorted(lean_object* v_k_185_, lean_object* v_m_186_, lean_object* v_p_187_){
_start:
{
if (lean_obj_tag(v_p_187_) == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_k_185_);
lean_ctor_set(v___x_188_, 1, v_m_186_);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_p_187_);
return v___x_189_;
}
else
{
lean_object* v_head_190_; lean_object* v_tail_191_; lean_object* v_snd_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_head_190_ = lean_ctor_get(v_p_187_, 0);
lean_inc(v_head_190_);
v_tail_191_ = lean_ctor_get(v_p_187_, 1);
v_snd_192_ = lean_ctor_get(v_head_190_, 1);
v___x_193_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_194_ = ((lean_object*)(l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go___closed__0));
lean_inc(v_snd_192_);
lean_inc(v_m_186_);
v___x_195_ = l_List_decidableLex___redArg(v___x_193_, v___x_194_, v_m_186_, v_snd_192_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
lean_inc(v_tail_191_);
v_isSharedCheck_203_ = !lean_is_exclusive(v_p_187_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; lean_object* v_unused_205_; 
v_unused_204_ = lean_ctor_get(v_p_187_, 1);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_p_187_, 0);
lean_dec(v_unused_205_);
v___x_197_ = v_p_187_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_dec(v_p_187_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = l_Nat_Internal_SOM_Poly_insertSorted(v_k_185_, v_m_186_, v_tail_191_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_head_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_isSharedCheck_213_ = !lean_is_exclusive(v_head_190_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; 
v_unused_214_ = lean_ctor_get(v_head_190_, 1);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_head_190_, 0);
lean_dec(v_unused_215_);
v___x_207_ = v_head_190_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_head_190_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_m_186_);
lean_ctor_set(v___x_207_, 0, v_k_185_);
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_k_185_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_m_186_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_p_187_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mulMon_go(lean_object* v_k_216_, lean_object* v_m_217_, lean_object* v_p_218_, lean_object* v_acc_219_){
_start:
{
if (lean_obj_tag(v_p_218_) == 0)
{
lean_dec(v_m_217_);
return v_acc_219_;
}
else
{
lean_object* v_head_220_; lean_object* v_tail_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_head_220_ = lean_ctor_get(v_p_218_, 0);
lean_inc(v_head_220_);
v_tail_221_ = lean_ctor_get(v_p_218_, 1);
lean_inc(v_tail_221_);
lean_dec_ref_known(v_p_218_, 2);
v_fst_222_ = lean_ctor_get(v_head_220_, 0);
lean_inc(v_fst_222_);
v_snd_223_ = lean_ctor_get(v_head_220_, 1);
lean_inc(v_snd_223_);
lean_dec(v_head_220_);
v___x_224_ = lean_nat_mul(v_k_216_, v_fst_222_);
lean_dec(v_fst_222_);
lean_inc(v_m_217_);
v___x_225_ = l_Nat_Internal_SOM_Mon_mul(v_m_217_, v_snd_223_);
v___x_226_ = l_Nat_Internal_SOM_Poly_insertSorted(v___x_224_, v___x_225_, v_acc_219_);
v_p_218_ = v_tail_221_;
v_acc_219_ = v___x_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mulMon_go___boxed(lean_object* v_k_228_, lean_object* v_m_229_, lean_object* v_p_230_, lean_object* v_acc_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mulMon_go(v_k_228_, v_m_229_, v_p_230_, v_acc_231_);
lean_dec(v_k_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_mulMon(lean_object* v_p_233_, lean_object* v_k_234_, lean_object* v_m_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_box(0);
v___x_237_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mulMon_go(v_k_234_, v_m_235_, v_p_233_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_mulMon___boxed(lean_object* v_p_238_, lean_object* v_k_239_, lean_object* v_m_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Nat_Internal_SOM_Poly_mulMon(v_p_238_, v_k_239_, v_m_240_);
lean_dec(v_k_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mul_go(lean_object* v_p_u2082_242_, lean_object* v_p_u2081_243_, lean_object* v_acc_244_){
_start:
{
if (lean_obj_tag(v_p_u2081_243_) == 0)
{
lean_dec(v_p_u2082_242_);
return v_acc_244_;
}
else
{
lean_object* v_head_245_; lean_object* v_tail_246_; lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_head_245_ = lean_ctor_get(v_p_u2081_243_, 0);
lean_inc(v_head_245_);
v_tail_246_ = lean_ctor_get(v_p_u2081_243_, 1);
lean_inc(v_tail_246_);
lean_dec_ref_known(v_p_u2081_243_, 2);
v_fst_247_ = lean_ctor_get(v_head_245_, 0);
lean_inc(v_fst_247_);
v_snd_248_ = lean_ctor_get(v_head_245_, 1);
lean_inc(v_snd_248_);
lean_dec(v_head_245_);
lean_inc(v_p_u2082_242_);
v___x_249_ = l_Nat_Internal_SOM_Poly_mulMon(v_p_u2082_242_, v_fst_247_, v_snd_248_);
lean_dec(v_fst_247_);
v___x_250_ = l_Nat_Internal_SOM_Poly_add(v_acc_244_, v___x_249_);
v_p_u2081_243_ = v_tail_246_;
v_acc_244_ = v___x_250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Poly_mul(lean_object* v_p_u2081_252_, lean_object* v_p_u2082_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(0);
v___x_255_ = l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_mul_go(v_p_u2082_253_, v_p_u2081_252_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_toPoly(lean_object* v_x_256_){
_start:
{
switch(lean_obj_tag(v_x_256_))
{
case 0:
{
lean_object* v_i_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_i_257_ = lean_ctor_get(v_x_256_, 0);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_nat_dec_eq(v_i_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
lean_inc(v_i_257_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_i_257_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
case 1:
{
lean_object* v_v_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_v_264_ = lean_ctor_get(v_x_256_, 0);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_box(0);
lean_inc(v_v_264_);
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v_v_264_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_266_);
return v___x_269_;
}
case 2:
{
lean_object* v_a_270_; lean_object* v_b_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_a_270_ = lean_ctor_get(v_x_256_, 0);
v_b_271_ = lean_ctor_get(v_x_256_, 1);
v___x_272_ = l_Nat_Internal_SOM_Expr_toPoly(v_a_270_);
v___x_273_ = l_Nat_Internal_SOM_Expr_toPoly(v_b_271_);
v___x_274_ = l_Nat_Internal_SOM_Poly_add(v___x_272_, v___x_273_);
return v___x_274_;
}
default: 
{
lean_object* v_a_275_; lean_object* v_b_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_a_275_ = lean_ctor_get(v_x_256_, 0);
v_b_276_ = lean_ctor_get(v_x_256_, 1);
v___x_277_ = l_Nat_Internal_SOM_Expr_toPoly(v_a_275_);
v___x_278_ = l_Nat_Internal_SOM_Expr_toPoly(v_b_276_);
v___x_279_ = l_Nat_Internal_SOM_Poly_mul(v___x_277_, v___x_278_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_SOM_Expr_toPoly___boxed(lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Nat_Internal_SOM_Expr_toPoly(v_x_280_);
lean_dec_ref(v_x_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_282_, lean_object* v_m_u2082_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_, lean_object* v_h__3_286_){
_start:
{
if (lean_obj_tag(v_m_u2082_283_) == 0)
{
lean_object* v___x_287_; 
lean_dec(v_h__3_286_);
lean_dec(v_h__2_285_);
v___x_287_ = lean_apply_1(v_h__1_284_, v_m_u2081_282_);
return v___x_287_;
}
else
{
lean_dec(v_h__1_284_);
if (lean_obj_tag(v_m_u2081_282_) == 0)
{
lean_object* v___x_288_; 
lean_dec(v_h__3_286_);
v___x_288_ = lean_apply_2(v_h__2_285_, v_m_u2082_283_, lean_box(0));
return v___x_288_;
}
else
{
lean_object* v_head_289_; lean_object* v_tail_290_; lean_object* v_head_291_; lean_object* v_tail_292_; lean_object* v___x_293_; 
lean_dec(v_h__2_285_);
v_head_289_ = lean_ctor_get(v_m_u2082_283_, 0);
lean_inc(v_head_289_);
v_tail_290_ = lean_ctor_get(v_m_u2082_283_, 1);
lean_inc(v_tail_290_);
lean_dec_ref_known(v_m_u2082_283_, 2);
v_head_291_ = lean_ctor_get(v_m_u2081_282_, 0);
lean_inc(v_head_291_);
v_tail_292_ = lean_ctor_get(v_m_u2081_282_, 1);
lean_inc(v_tail_292_);
lean_dec_ref_known(v_m_u2081_282_, 2);
v___x_293_ = lean_apply_4(v_h__3_286_, v_head_291_, v_tail_292_, v_head_289_, v_tail_290_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Mon_mul_go_match__1_splitter(lean_object* v_motive_294_, lean_object* v_m_u2081_295_, lean_object* v_m_u2082_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_, lean_object* v_h__3_299_){
_start:
{
if (lean_obj_tag(v_m_u2082_296_) == 0)
{
lean_object* v___x_300_; 
lean_dec(v_h__3_299_);
lean_dec(v_h__2_298_);
v___x_300_ = lean_apply_1(v_h__1_297_, v_m_u2081_295_);
return v___x_300_;
}
else
{
lean_dec(v_h__1_297_);
if (lean_obj_tag(v_m_u2081_295_) == 0)
{
lean_object* v___x_301_; 
lean_dec(v_h__3_299_);
v___x_301_ = lean_apply_2(v_h__2_298_, v_m_u2082_296_, lean_box(0));
return v___x_301_;
}
else
{
lean_object* v_head_302_; lean_object* v_tail_303_; lean_object* v_head_304_; lean_object* v_tail_305_; lean_object* v___x_306_; 
lean_dec(v_h__2_298_);
v_head_302_ = lean_ctor_get(v_m_u2082_296_, 0);
lean_inc(v_head_302_);
v_tail_303_ = lean_ctor_get(v_m_u2082_296_, 1);
lean_inc(v_tail_303_);
lean_dec_ref_known(v_m_u2082_296_, 2);
v_head_304_ = lean_ctor_get(v_m_u2081_295_, 0);
lean_inc(v_head_304_);
v_tail_305_ = lean_ctor_get(v_m_u2081_295_, 1);
lean_inc(v_tail_305_);
lean_dec_ref_known(v_m_u2081_295_, 2);
v___x_306_ = lean_apply_4(v_h__3_299_, v_head_304_, v_tail_305_, v_head_302_, v_tail_303_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go_match__1_splitter___redArg(lean_object* v_p_u2081_307_, lean_object* v_p_u2082_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_){
_start:
{
if (lean_obj_tag(v_p_u2082_308_) == 0)
{
lean_object* v___x_312_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__2_310_);
v___x_312_ = lean_apply_1(v_h__1_309_, v_p_u2081_307_);
return v___x_312_;
}
else
{
lean_dec(v_h__1_309_);
if (lean_obj_tag(v_p_u2081_307_) == 0)
{
lean_object* v___x_313_; 
lean_dec(v_h__3_311_);
v___x_313_ = lean_apply_2(v_h__2_310_, v_p_u2082_308_, lean_box(0));
return v___x_313_;
}
else
{
lean_object* v_head_314_; lean_object* v_head_315_; lean_object* v_tail_316_; lean_object* v_tail_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_322_; 
lean_dec(v_h__2_310_);
v_head_314_ = lean_ctor_get(v_p_u2081_307_, 0);
lean_inc(v_head_314_);
v_head_315_ = lean_ctor_get(v_p_u2082_308_, 0);
lean_inc(v_head_315_);
v_tail_316_ = lean_ctor_get(v_p_u2082_308_, 1);
lean_inc(v_tail_316_);
lean_dec_ref_known(v_p_u2082_308_, 2);
v_tail_317_ = lean_ctor_get(v_p_u2081_307_, 1);
lean_inc(v_tail_317_);
lean_dec_ref_known(v_p_u2081_307_, 2);
v_fst_318_ = lean_ctor_get(v_head_314_, 0);
lean_inc(v_fst_318_);
v_snd_319_ = lean_ctor_get(v_head_314_, 1);
lean_inc(v_snd_319_);
lean_dec(v_head_314_);
v_fst_320_ = lean_ctor_get(v_head_315_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_head_315_, 1);
lean_inc(v_snd_321_);
lean_dec(v_head_315_);
v___x_322_ = lean_apply_6(v_h__3_311_, v_fst_318_, v_snd_319_, v_tail_317_, v_fst_320_, v_snd_321_, v_tail_316_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Internal_SOM_0__Nat_Internal_SOM_Poly_add_go_match__1_splitter(lean_object* v_motive_323_, lean_object* v_p_u2081_324_, lean_object* v_p_u2082_325_, lean_object* v_h__1_326_, lean_object* v_h__2_327_, lean_object* v_h__3_328_){
_start:
{
if (lean_obj_tag(v_p_u2082_325_) == 0)
{
lean_object* v___x_329_; 
lean_dec(v_h__3_328_);
lean_dec(v_h__2_327_);
v___x_329_ = lean_apply_1(v_h__1_326_, v_p_u2081_324_);
return v___x_329_;
}
else
{
lean_dec(v_h__1_326_);
if (lean_obj_tag(v_p_u2081_324_) == 0)
{
lean_object* v___x_330_; 
lean_dec(v_h__3_328_);
v___x_330_ = lean_apply_2(v_h__2_327_, v_p_u2082_325_, lean_box(0));
return v___x_330_;
}
else
{
lean_object* v_head_331_; lean_object* v_head_332_; lean_object* v_tail_333_; lean_object* v_tail_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_339_; 
lean_dec(v_h__2_327_);
v_head_331_ = lean_ctor_get(v_p_u2081_324_, 0);
lean_inc(v_head_331_);
v_head_332_ = lean_ctor_get(v_p_u2082_325_, 0);
lean_inc(v_head_332_);
v_tail_333_ = lean_ctor_get(v_p_u2082_325_, 1);
lean_inc(v_tail_333_);
lean_dec_ref_known(v_p_u2082_325_, 2);
v_tail_334_ = lean_ctor_get(v_p_u2081_324_, 1);
lean_inc(v_tail_334_);
lean_dec_ref_known(v_p_u2081_324_, 2);
v_fst_335_ = lean_ctor_get(v_head_331_, 0);
lean_inc(v_fst_335_);
v_snd_336_ = lean_ctor_get(v_head_331_, 1);
lean_inc(v_snd_336_);
lean_dec(v_head_331_);
v_fst_337_ = lean_ctor_get(v_head_332_, 0);
lean_inc(v_fst_337_);
v_snd_338_ = lean_ctor_get(v_head_332_, 1);
lean_inc(v_snd_338_);
lean_dec(v_head_332_);
v___x_339_ = lean_apply_6(v_h__3_328_, v_fst_335_, v_snd_336_, v_tail_334_, v_fst_337_, v_snd_338_, v_tail_333_);
return v___x_339_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Internal_SOM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Internal_SOM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Internal_SOM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_SOM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Internal_SOM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Internal_SOM(builtin);
}
#ifdef __cplusplus
}
#endif
