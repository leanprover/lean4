// Lean compiler output
// Module: Init.Data.Nat.SOM
// Imports: public import Init.Data.Nat.Linear import Init.ByCases import Init.Data.List.BasicAux import Init.Data.Prod import Init.Meta
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
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_List_decidableLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_SOM_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_SOM_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Nat_SOM_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_SOM_instInhabitedExpr_default = (const lean_object*)&l_Nat_SOM_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_SOM_instInhabitedExpr = (const lean_object*)&l_Nat_SOM_instInhabitedExpr_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Nat_SOM_Expr_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 2:
{
lean_object* v_a_10_; lean_object* v_b_11_; lean_object* v___x_12_; 
v_a_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_a_10_);
v_b_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_b_11_);
lean_dec_ref(v_t_8_);
v___x_12_ = lean_apply_2(v_k_9_, v_a_10_, v_b_11_);
return v___x_12_;
}
case 3:
{
lean_object* v_a_13_; lean_object* v_b_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_a_13_);
v_b_14_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_b_14_);
lean_dec_ref(v_t_8_);
v___x_15_ = lean_apply_2(v_k_9_, v_a_13_, v_b_14_);
return v___x_15_;
}
default: 
{
lean_object* v_i_16_; lean_object* v___x_17_; 
v_i_16_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_i_16_);
lean_dec_ref(v_t_8_);
v___x_17_ = lean_apply_1(v_k_9_, v_i_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Nat_SOM_Expr_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim___redArg(lean_object* v_t_30_, lean_object* v_num_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_30_, v_num_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_num_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_34_, v_num_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim___redArg(lean_object* v_t_38_, lean_object* v_var_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_38_, v_var_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_var_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_42_, v_var_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim___redArg(lean_object* v_t_46_, lean_object* v_add_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_46_, v_add_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_add_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_50_, v_add_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim___redArg(lean_object* v_t_54_, lean_object* v_mul_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_54_, v_mul_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_mul_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_58_, v_mul_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(lean_object* v_fuel_66_, lean_object* v_m_u2081_67_, lean_object* v_m_u2082_68_){
_start:
{
lean_object* v_zero_69_; uint8_t v_isZero_70_; 
v_zero_69_ = lean_unsigned_to_nat(0u);
v_isZero_70_ = lean_nat_dec_eq(v_fuel_66_, v_zero_69_);
if (v_isZero_70_ == 1)
{
lean_object* v___x_71_; 
v___x_71_ = l_List_appendTR___redArg(v_m_u2081_67_, v_m_u2082_68_);
return v___x_71_;
}
else
{
if (lean_obj_tag(v_m_u2082_68_) == 0)
{
return v_m_u2081_67_;
}
else
{
if (lean_obj_tag(v_m_u2081_67_) == 0)
{
return v_m_u2082_68_;
}
else
{
lean_object* v_head_72_; lean_object* v_tail_73_; lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v_one_76_; lean_object* v_n_77_; uint8_t v___x_78_; 
v_head_72_ = lean_ctor_get(v_m_u2082_68_, 0);
v_tail_73_ = lean_ctor_get(v_m_u2082_68_, 1);
v_head_74_ = lean_ctor_get(v_m_u2081_67_, 0);
v_tail_75_ = lean_ctor_get(v_m_u2081_67_, 1);
v_one_76_ = lean_unsigned_to_nat(1u);
v_n_77_ = lean_nat_sub(v_fuel_66_, v_one_76_);
v___x_78_ = l_Nat_blt(v_head_74_, v_head_72_);
if (v___x_78_ == 0)
{
lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_100_; 
lean_inc(v_tail_73_);
lean_inc(v_head_72_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_u2082_68_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_u2082_68_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_u2082_68_, 0);
lean_dec(v_unused_102_);
v___x_80_ = v_m_u2082_68_;
v_isShared_81_ = v_isSharedCheck_100_;
goto v_resetjp_79_;
}
else
{
lean_dec(v_m_u2082_68_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_100_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; 
v___x_82_ = l_Nat_blt(v_head_72_, v_head_74_);
if (v___x_82_ == 0)
{
lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_93_; 
lean_inc(v_tail_75_);
lean_inc(v_head_74_);
v_isSharedCheck_93_ = !lean_is_exclusive(v_m_u2081_67_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; lean_object* v_unused_95_; 
v_unused_94_ = lean_ctor_get(v_m_u2081_67_, 1);
lean_dec(v_unused_94_);
v_unused_95_ = lean_ctor_get(v_m_u2081_67_, 0);
lean_dec(v_unused_95_);
v___x_84_ = v_m_u2081_67_;
v_isShared_85_ = v_isSharedCheck_93_;
goto v_resetjp_83_;
}
else
{
lean_dec(v_m_u2081_67_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_93_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(v_n_77_, v_tail_75_, v_tail_73_);
lean_dec(v_n_77_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_86_);
lean_ctor_set(v___x_84_, 0, v_head_72_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_head_72_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_86_);
v___x_88_ = v_reuseFailAlloc_92_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_88_);
lean_ctor_set(v___x_80_, 0, v_head_74_);
v___x_90_ = v___x_80_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_head_74_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(v_n_77_, v_m_u2081_67_, v_tail_73_);
lean_dec(v_n_77_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_96_);
v___x_98_ = v___x_80_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_head_72_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
lean_inc(v_tail_75_);
lean_inc(v_head_74_);
v_isSharedCheck_110_ = !lean_is_exclusive(v_m_u2081_67_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_111_ = lean_ctor_get(v_m_u2081_67_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_m_u2081_67_, 0);
lean_dec(v_unused_112_);
v___x_104_ = v_m_u2081_67_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_dec(v_m_u2081_67_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(v_n_77_, v_tail_75_, v_m_u2082_68_);
lean_dec(v_n_77_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_106_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_head_74_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go___boxed(lean_object* v_fuel_113_, lean_object* v_m_u2081_114_, lean_object* v_m_u2082_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(v_fuel_113_, v_m_u2081_114_, v_m_u2082_115_);
lean_dec(v_fuel_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object* v_m_u2081_117_, lean_object* v_m_u2082_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1000000u);
v___x_120_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(v___x_119_, v_m_u2081_117_, v_m_u2082_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(lean_object* v_fuel_122_, lean_object* v_p_u2081_123_, lean_object* v_p_u2082_124_){
_start:
{
lean_object* v_zero_125_; uint8_t v_isZero_126_; 
v_zero_125_ = lean_unsigned_to_nat(0u);
v_isZero_126_ = lean_nat_dec_eq(v_fuel_122_, v_zero_125_);
if (v_isZero_126_ == 1)
{
lean_object* v___x_127_; 
lean_dec(v_fuel_122_);
v___x_127_ = l_List_appendTR___redArg(v_p_u2081_123_, v_p_u2082_124_);
return v___x_127_;
}
else
{
if (lean_obj_tag(v_p_u2082_124_) == 0)
{
lean_dec(v_fuel_122_);
return v_p_u2081_123_;
}
else
{
if (lean_obj_tag(v_p_u2081_123_) == 0)
{
lean_dec(v_fuel_122_);
return v_p_u2082_124_;
}
else
{
lean_object* v_head_128_; lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v_tail_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v_fst_134_; lean_object* v_snd_135_; lean_object* v_one_136_; lean_object* v_n_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_head_128_ = lean_ctor_get(v_p_u2081_123_, 0);
v_head_129_ = lean_ctor_get(v_p_u2082_124_, 0);
lean_inc(v_head_129_);
v_tail_130_ = lean_ctor_get(v_p_u2082_124_, 1);
v_tail_131_ = lean_ctor_get(v_p_u2081_123_, 1);
v_fst_132_ = lean_ctor_get(v_head_128_, 0);
v_snd_133_ = lean_ctor_get(v_head_128_, 1);
v_fst_134_ = lean_ctor_get(v_head_129_, 0);
v_snd_135_ = lean_ctor_get(v_head_129_, 1);
v_one_136_ = lean_unsigned_to_nat(1u);
v_n_137_ = lean_nat_sub(v_fuel_122_, v_one_136_);
lean_dec(v_fuel_122_);
v___x_138_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_139_ = ((lean_object*)(l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0));
lean_inc(v_snd_135_);
lean_inc(v_snd_133_);
lean_inc_ref(v___x_138_);
v___x_140_ = l_List_decidableLex___redArg(v___x_138_, v___x_139_, v_snd_133_, v_snd_135_);
if (v___x_140_ == 0)
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_171_; 
lean_inc(v_tail_130_);
v_isSharedCheck_171_ = !lean_is_exclusive(v_p_u2082_124_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; 
v_unused_172_ = lean_ctor_get(v_p_u2082_124_, 1);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_p_u2082_124_, 0);
lean_dec(v_unused_173_);
v___x_142_ = v_p_u2082_124_;
v_isShared_143_ = v_isSharedCheck_171_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_p_u2082_124_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_171_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
uint8_t v___x_144_; 
lean_inc(v_snd_133_);
lean_inc(v_snd_135_);
v___x_144_ = l_List_decidableLex___redArg(v___x_138_, v___x_139_, v_snd_135_, v_snd_133_);
if (v___x_144_ == 0)
{
lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_164_; 
lean_inc(v_fst_134_);
lean_inc(v_snd_133_);
lean_inc(v_fst_132_);
lean_inc(v_tail_131_);
lean_del_object(v___x_142_);
v_isSharedCheck_164_ = !lean_is_exclusive(v_p_u2081_123_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; lean_object* v_unused_166_; 
v_unused_165_ = lean_ctor_get(v_p_u2081_123_, 1);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_p_u2081_123_, 0);
lean_dec(v_unused_166_);
v___x_146_ = v_p_u2081_123_;
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
else
{
lean_dec(v_p_u2081_123_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_161_; 
v_isSharedCheck_161_ = !lean_is_exclusive(v_head_129_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; 
v_unused_162_ = lean_ctor_get(v_head_129_, 1);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_head_129_, 0);
lean_dec(v_unused_163_);
v___x_149_ = v_head_129_;
v_isShared_150_ = v_isSharedCheck_161_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_head_129_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_161_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_nat_add(v_fst_132_, v_fst_134_);
lean_dec(v_fst_134_);
lean_dec(v_fst_132_);
v___x_152_ = lean_nat_dec_eq(v___x_151_, v_zero_125_);
if (v___x_152_ == 0)
{
lean_object* v___x_154_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v_snd_133_);
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_snd_133_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(v_n_137_, v_tail_131_, v_tail_130_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_155_);
lean_ctor_set(v___x_146_, 0, v___x_154_);
v___x_157_ = v___x_146_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_dec(v___x_151_);
lean_del_object(v___x_149_);
lean_del_object(v___x_146_);
lean_dec(v_snd_133_);
v_fuel_122_ = v_n_137_;
v_p_u2081_123_ = v_tail_131_;
v_p_u2082_124_ = v_tail_130_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(v_n_137_, v_p_u2081_123_, v_tail_130_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_167_);
v___x_169_ = v___x_142_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_head_129_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
lean_inc(v_tail_131_);
lean_inc(v_head_128_);
lean_dec_ref(v___x_138_);
lean_dec(v_head_129_);
v_isSharedCheck_181_ = !lean_is_exclusive(v_p_u2081_123_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_182_ = lean_ctor_get(v_p_u2081_123_, 1);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_p_u2081_123_, 0);
lean_dec(v_unused_183_);
v___x_175_ = v_p_u2081_123_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_dec(v_p_u2081_123_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(v_n_137_, v_tail_131_, v_p_u2082_124_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_head_128_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object* v_p_u2081_184_, lean_object* v_p_u2082_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(1000000u);
v___x_187_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(v___x_186_, v_p_u2081_184_, v_p_u2082_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object* v_k_188_, lean_object* v_m_189_, lean_object* v_p_190_){
_start:
{
if (lean_obj_tag(v_p_190_) == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_k_188_);
lean_ctor_set(v___x_191_, 1, v_m_189_);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_p_190_);
return v___x_192_;
}
else
{
lean_object* v_head_193_; lean_object* v_tail_194_; lean_object* v_snd_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_head_193_ = lean_ctor_get(v_p_190_, 0);
lean_inc(v_head_193_);
v_tail_194_ = lean_ctor_get(v_p_190_, 1);
v_snd_195_ = lean_ctor_get(v_head_193_, 1);
v___x_196_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_197_ = ((lean_object*)(l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0));
lean_inc(v_snd_195_);
lean_inc(v_m_189_);
v___x_198_ = l_List_decidableLex___redArg(v___x_196_, v___x_197_, v_m_189_, v_snd_195_);
if (v___x_198_ == 0)
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
lean_inc(v_tail_194_);
v_isSharedCheck_206_ = !lean_is_exclusive(v_p_190_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_207_ = lean_ctor_get(v_p_190_, 1);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_p_190_, 0);
lean_dec(v_unused_208_);
v___x_200_ = v_p_190_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_p_190_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = l_Nat_SOM_Poly_insertSorted(v_k_188_, v_m_189_, v_tail_194_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_head_193_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_216_; 
v_isSharedCheck_216_ = !lean_is_exclusive(v_head_193_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_217_ = lean_ctor_get(v_head_193_, 1);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_head_193_, 0);
lean_dec(v_unused_218_);
v___x_210_ = v_head_193_;
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
else
{
lean_dec(v_head_193_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_m_189_);
lean_ctor_set(v___x_210_, 0, v_k_188_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_k_188_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_m_189_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_p_190_);
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(lean_object* v_k_219_, lean_object* v_m_220_, lean_object* v_p_221_, lean_object* v_acc_222_){
_start:
{
if (lean_obj_tag(v_p_221_) == 0)
{
lean_dec(v_m_220_);
return v_acc_222_;
}
else
{
lean_object* v_head_223_; lean_object* v_tail_224_; lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_head_223_ = lean_ctor_get(v_p_221_, 0);
lean_inc(v_head_223_);
v_tail_224_ = lean_ctor_get(v_p_221_, 1);
lean_inc(v_tail_224_);
lean_dec_ref(v_p_221_);
v_fst_225_ = lean_ctor_get(v_head_223_, 0);
lean_inc(v_fst_225_);
v_snd_226_ = lean_ctor_get(v_head_223_, 1);
lean_inc(v_snd_226_);
lean_dec(v_head_223_);
v___x_227_ = lean_nat_mul(v_k_219_, v_fst_225_);
lean_dec(v_fst_225_);
lean_inc(v_m_220_);
v___x_228_ = l_Nat_SOM_Mon_mul(v_m_220_, v_snd_226_);
v___x_229_ = l_Nat_SOM_Poly_insertSorted(v___x_227_, v___x_228_, v_acc_222_);
v_p_221_ = v_tail_224_;
v_acc_222_ = v___x_229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go___boxed(lean_object* v_k_231_, lean_object* v_m_232_, lean_object* v_p_233_, lean_object* v_acc_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(v_k_231_, v_m_232_, v_p_233_, v_acc_234_);
lean_dec(v_k_231_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object* v_p_236_, lean_object* v_k_237_, lean_object* v_m_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(v_k_237_, v_m_238_, v_p_236_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon___boxed(lean_object* v_p_241_, lean_object* v_k_242_, lean_object* v_m_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Nat_SOM_Poly_mulMon(v_p_241_, v_k_242_, v_m_243_);
lean_dec(v_k_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(lean_object* v_p_u2082_245_, lean_object* v_p_u2081_246_, lean_object* v_acc_247_){
_start:
{
if (lean_obj_tag(v_p_u2081_246_) == 0)
{
lean_dec(v_p_u2082_245_);
return v_acc_247_;
}
else
{
lean_object* v_head_248_; lean_object* v_tail_249_; lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_head_248_ = lean_ctor_get(v_p_u2081_246_, 0);
lean_inc(v_head_248_);
v_tail_249_ = lean_ctor_get(v_p_u2081_246_, 1);
lean_inc(v_tail_249_);
lean_dec_ref(v_p_u2081_246_);
v_fst_250_ = lean_ctor_get(v_head_248_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_head_248_, 1);
lean_inc(v_snd_251_);
lean_dec(v_head_248_);
lean_inc(v_p_u2082_245_);
v___x_252_ = l_Nat_SOM_Poly_mulMon(v_p_u2082_245_, v_fst_250_, v_snd_251_);
lean_dec(v_fst_250_);
v___x_253_ = l_Nat_SOM_Poly_add(v_acc_247_, v___x_252_);
v_p_u2081_246_ = v_tail_249_;
v_acc_247_ = v___x_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul(lean_object* v_p_u2081_255_, lean_object* v_p_u2082_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(0);
v___x_258_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(v_p_u2082_256_, v_p_u2081_255_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly(lean_object* v_x_259_){
_start:
{
switch(lean_obj_tag(v_x_259_))
{
case 0:
{
lean_object* v_i_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_i_260_ = lean_ctor_get(v_x_259_, 0);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_nat_dec_eq(v_i_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
lean_inc(v_i_260_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_i_260_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
case 1:
{
lean_object* v_v_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_v_267_ = lean_ctor_get(v_x_259_, 0);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_box(0);
lean_inc(v_v_267_);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v_v_267_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_268_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_269_);
return v___x_272_;
}
case 2:
{
lean_object* v_a_273_; lean_object* v_b_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_a_273_ = lean_ctor_get(v_x_259_, 0);
v_b_274_ = lean_ctor_get(v_x_259_, 1);
v___x_275_ = l_Nat_SOM_Expr_toPoly(v_a_273_);
v___x_276_ = l_Nat_SOM_Expr_toPoly(v_b_274_);
v___x_277_ = l_Nat_SOM_Poly_add(v___x_275_, v___x_276_);
return v___x_277_;
}
default: 
{
lean_object* v_a_278_; lean_object* v_b_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_a_278_ = lean_ctor_get(v_x_259_, 0);
v_b_279_ = lean_ctor_get(v_x_259_, 1);
v___x_280_ = l_Nat_SOM_Expr_toPoly(v_a_278_);
v___x_281_ = l_Nat_SOM_Expr_toPoly(v_b_279_);
v___x_282_ = l_Nat_SOM_Poly_mul(v___x_280_, v___x_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object* v_x_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Nat_SOM_Expr_toPoly(v_x_283_);
lean_dec_ref(v_x_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_285_, lean_object* v_m_u2082_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_, lean_object* v_h__3_289_){
_start:
{
if (lean_obj_tag(v_m_u2082_286_) == 0)
{
lean_object* v___x_290_; 
lean_dec(v_h__3_289_);
lean_dec(v_h__2_288_);
v___x_290_ = lean_apply_1(v_h__1_287_, v_m_u2081_285_);
return v___x_290_;
}
else
{
lean_dec(v_h__1_287_);
if (lean_obj_tag(v_m_u2081_285_) == 0)
{
lean_object* v___x_291_; 
lean_dec(v_h__3_289_);
v___x_291_ = lean_apply_2(v_h__2_288_, v_m_u2082_286_, lean_box(0));
return v___x_291_;
}
else
{
lean_object* v_head_292_; lean_object* v_tail_293_; lean_object* v_head_294_; lean_object* v_tail_295_; lean_object* v___x_296_; 
lean_dec(v_h__2_288_);
v_head_292_ = lean_ctor_get(v_m_u2082_286_, 0);
lean_inc(v_head_292_);
v_tail_293_ = lean_ctor_get(v_m_u2082_286_, 1);
lean_inc(v_tail_293_);
lean_dec_ref(v_m_u2082_286_);
v_head_294_ = lean_ctor_get(v_m_u2081_285_, 0);
lean_inc(v_head_294_);
v_tail_295_ = lean_ctor_get(v_m_u2081_285_, 1);
lean_inc(v_tail_295_);
lean_dec_ref(v_m_u2081_285_);
v___x_296_ = lean_apply_4(v_h__3_289_, v_head_294_, v_tail_295_, v_head_292_, v_tail_293_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object* v_motive_297_, lean_object* v_m_u2081_298_, lean_object* v_m_u2082_299_, lean_object* v_h__1_300_, lean_object* v_h__2_301_, lean_object* v_h__3_302_){
_start:
{
if (lean_obj_tag(v_m_u2082_299_) == 0)
{
lean_object* v___x_303_; 
lean_dec(v_h__3_302_);
lean_dec(v_h__2_301_);
v___x_303_ = lean_apply_1(v_h__1_300_, v_m_u2081_298_);
return v___x_303_;
}
else
{
lean_dec(v_h__1_300_);
if (lean_obj_tag(v_m_u2081_298_) == 0)
{
lean_object* v___x_304_; 
lean_dec(v_h__3_302_);
v___x_304_ = lean_apply_2(v_h__2_301_, v_m_u2082_299_, lean_box(0));
return v___x_304_;
}
else
{
lean_object* v_head_305_; lean_object* v_tail_306_; lean_object* v_head_307_; lean_object* v_tail_308_; lean_object* v___x_309_; 
lean_dec(v_h__2_301_);
v_head_305_ = lean_ctor_get(v_m_u2082_299_, 0);
lean_inc(v_head_305_);
v_tail_306_ = lean_ctor_get(v_m_u2082_299_, 1);
lean_inc(v_tail_306_);
lean_dec_ref(v_m_u2082_299_);
v_head_307_ = lean_ctor_get(v_m_u2081_298_, 0);
lean_inc(v_head_307_);
v_tail_308_ = lean_ctor_get(v_m_u2081_298_, 1);
lean_inc(v_tail_308_);
lean_dec_ref(v_m_u2081_298_);
v___x_309_ = lean_apply_4(v_h__3_302_, v_head_307_, v_tail_308_, v_head_305_, v_tail_306_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(lean_object* v_p_u2081_310_, lean_object* v_p_u2082_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_, lean_object* v_h__3_314_){
_start:
{
if (lean_obj_tag(v_p_u2082_311_) == 0)
{
lean_object* v___x_315_; 
lean_dec(v_h__3_314_);
lean_dec(v_h__2_313_);
v___x_315_ = lean_apply_1(v_h__1_312_, v_p_u2081_310_);
return v___x_315_;
}
else
{
lean_dec(v_h__1_312_);
if (lean_obj_tag(v_p_u2081_310_) == 0)
{
lean_object* v___x_316_; 
lean_dec(v_h__3_314_);
v___x_316_ = lean_apply_2(v_h__2_313_, v_p_u2082_311_, lean_box(0));
return v___x_316_;
}
else
{
lean_object* v_head_317_; lean_object* v_head_318_; lean_object* v_tail_319_; lean_object* v_tail_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v___x_325_; 
lean_dec(v_h__2_313_);
v_head_317_ = lean_ctor_get(v_p_u2081_310_, 0);
lean_inc(v_head_317_);
v_head_318_ = lean_ctor_get(v_p_u2082_311_, 0);
lean_inc(v_head_318_);
v_tail_319_ = lean_ctor_get(v_p_u2082_311_, 1);
lean_inc(v_tail_319_);
lean_dec_ref(v_p_u2082_311_);
v_tail_320_ = lean_ctor_get(v_p_u2081_310_, 1);
lean_inc(v_tail_320_);
lean_dec_ref(v_p_u2081_310_);
v_fst_321_ = lean_ctor_get(v_head_317_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v_head_317_, 1);
lean_inc(v_snd_322_);
lean_dec(v_head_317_);
v_fst_323_ = lean_ctor_get(v_head_318_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v_head_318_, 1);
lean_inc(v_snd_324_);
lean_dec(v_head_318_);
v___x_325_ = lean_apply_6(v_h__3_314_, v_fst_321_, v_snd_322_, v_tail_320_, v_fst_323_, v_snd_324_, v_tail_319_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object* v_motive_326_, lean_object* v_p_u2081_327_, lean_object* v_p_u2082_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_, lean_object* v_h__3_331_){
_start:
{
if (lean_obj_tag(v_p_u2082_328_) == 0)
{
lean_object* v___x_332_; 
lean_dec(v_h__3_331_);
lean_dec(v_h__2_330_);
v___x_332_ = lean_apply_1(v_h__1_329_, v_p_u2081_327_);
return v___x_332_;
}
else
{
lean_dec(v_h__1_329_);
if (lean_obj_tag(v_p_u2081_327_) == 0)
{
lean_object* v___x_333_; 
lean_dec(v_h__3_331_);
v___x_333_ = lean_apply_2(v_h__2_330_, v_p_u2082_328_, lean_box(0));
return v___x_333_;
}
else
{
lean_object* v_head_334_; lean_object* v_head_335_; lean_object* v_tail_336_; lean_object* v_tail_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_342_; 
lean_dec(v_h__2_330_);
v_head_334_ = lean_ctor_get(v_p_u2081_327_, 0);
lean_inc(v_head_334_);
v_head_335_ = lean_ctor_get(v_p_u2082_328_, 0);
lean_inc(v_head_335_);
v_tail_336_ = lean_ctor_get(v_p_u2082_328_, 1);
lean_inc(v_tail_336_);
lean_dec_ref(v_p_u2082_328_);
v_tail_337_ = lean_ctor_get(v_p_u2081_327_, 1);
lean_inc(v_tail_337_);
lean_dec_ref(v_p_u2081_327_);
v_fst_338_ = lean_ctor_get(v_head_334_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_head_334_, 1);
lean_inc(v_snd_339_);
lean_dec(v_head_334_);
v_fst_340_ = lean_ctor_get(v_head_335_, 0);
lean_inc(v_fst_340_);
v_snd_341_ = lean_ctor_get(v_head_335_, 1);
lean_inc(v_snd_341_);
lean_dec(v_head_335_);
v___x_342_ = lean_apply_6(v_h__3_331_, v_fst_338_, v_snd_339_, v_tail_337_, v_fst_340_, v_snd_341_, v_tail_336_);
return v___x_342_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_SOM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_SOM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_SOM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Linear(builtin);
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
res = runtime_initialize_Init_Data_Nat_SOM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_SOM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_SOM(builtin);
}
#ifdef __cplusplus
}
#endif
