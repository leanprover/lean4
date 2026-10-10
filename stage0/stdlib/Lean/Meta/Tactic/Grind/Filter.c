// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Filter
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_true_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_true_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_gen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_gen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_or_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_or_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_and_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_and_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_not_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_not_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_Filter_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
return v_k_6_;
}
case 3:
{
lean_object* v_pred_7_; lean_object* v___x_8_; 
v_pred_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_pred_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_pred_7_);
return v___x_8_;
}
case 4:
{
lean_object* v_a_9_; lean_object* v_b_10_; lean_object* v___x_11_; 
v_a_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_9_);
v_b_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_b_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_a_9_, v_b_10_);
return v___x_11_;
}
case 5:
{
lean_object* v_a_12_; lean_object* v_b_13_; lean_object* v___x_14_; 
v_a_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_12_);
v_b_13_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_b_13_);
lean_dec_ref_known(v_t_5_, 2);
v___x_14_ = lean_apply_2(v_k_6_, v_a_12_, v_b_13_);
return v___x_14_;
}
default: 
{
lean_object* v_declName_15_; lean_object* v___x_16_; 
v_declName_15_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_declName_15_);
lean_dec(v_t_5_);
v___x_16_ = lean_apply_1(v_k_6_, v_declName_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Filter_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_true_elim___redArg(lean_object* v_t_29_, lean_object* v_true_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_29_, v_true_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_true_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_true_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_33_, v_true_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_const_elim___redArg(lean_object* v_t_37_, lean_object* v_const_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_37_, v_const_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_const_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_const_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_41_, v_const_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_fvar_elim___redArg(lean_object* v_t_45_, lean_object* v_fvar_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_45_, v_fvar_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_fvar_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_fvar_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_49_, v_fvar_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_gen_elim___redArg(lean_object* v_t_53_, lean_object* v_gen_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_53_, v_gen_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_gen_elim(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_gen_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_57_, v_gen_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_or_elim___redArg(lean_object* v_t_61_, lean_object* v_or_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_61_, v_or_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_or_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_or_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_65_, v_or_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_and_elim___redArg(lean_object* v_t_69_, lean_object* v_and_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_69_, v_and_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_and_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_and_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_73_, v_and_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_not_elim___redArg(lean_object* v_t_77_, lean_object* v_not_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_77_, v_not_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_not_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_not_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_81_, v_not_83_);
return v___x_84_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(lean_object* v_e_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_88_, v_a_89_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; uint8_t v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = lean_unbox(v_a_96_);
lean_dec(v_a_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_88_, v_a_90_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = l_Lean_Expr_cleanupAnnotations(v_a_99_);
v___x_101_ = l_Lean_Expr_isApp(v___x_100_);
if (v___x_101_ == 0)
{
lean_dec_ref(v___x_100_);
goto v___jp_92_;
}
else
{
lean_object* v_arg_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_arg_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc_ref(v_arg_102_);
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_100_);
v___x_104_ = l_Lean_Expr_isApp(v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v___x_103_);
lean_dec_ref(v_arg_102_);
goto v___jp_92_;
}
else
{
lean_object* v_arg_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_arg_105_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_arg_105_);
v___x_106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_103_);
v___x_107_ = l_Lean_Expr_isApp(v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v___x_106_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_102_);
goto v___jp_92_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_106_);
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1));
v___x_110_ = l_Lean_Expr_isConstOf(v___x_108_, v___x_109_);
lean_dec_ref(v___x_108_);
if (v___x_110_ == 0)
{
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_102_);
goto v___jp_92_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_105_, v_a_89_);
lean_dec_ref(v_arg_105_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_102_, v_a_89_);
lean_dec_ref(v_arg_102_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; uint8_t v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v___x_115_ = lean_nat_dec_le(v_a_112_, v_a_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_122_ == 0)
{
lean_object* v_unused_123_; 
v_unused_123_ = lean_ctor_get(v___x_113_, 0);
lean_dec(v_unused_123_);
v___x_117_ = v___x_113_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_dec(v___x_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_a_112_);
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_112_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_dec(v_a_112_);
return v___x_113_;
}
}
else
{
lean_dec(v_a_112_);
return v___x_113_;
}
}
else
{
lean_dec_ref(v_arg_102_);
return v___x_111_;
}
}
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_98_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_98_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_88_, v_a_89_);
lean_dec_ref(v_e_88_);
return v___x_132_;
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec_ref(v_e_88_);
v_a_133_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_95_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_95_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
v___jp_92_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v_res_141_;
v_res_141_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_88_, v_a_89_, v_a_90_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___boxed(lean_object* v_e_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec(v_a_143_);
return v_res_146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(lean_object* v_e_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_147_, v_a_148_, v_a_155_);
return v___x_159_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_147_ = stack[0].m_obj;
lean_object* v_a_148_ = stack[1].m_obj;
lean_object* v_a_149_ = stack[2].m_obj;
lean_object* v_a_150_ = stack[3].m_obj;
lean_object* v_a_151_ = stack[4].m_obj;
lean_object* v_a_152_ = stack[5].m_obj;
lean_object* v_a_153_ = stack[6].m_obj;
lean_object* v_a_154_ = stack[7].m_obj;
lean_object* v_a_155_ = stack[8].m_obj;
lean_object* v_a_156_ = stack[9].m_obj;
lean_object* v_a_157_ = stack[10].m_obj;
lean_object* v_res_160_;
v_res_160_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(v_e_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___boxed(lean_object* v_e_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(v_e_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec(v_a_162_);
return v_res_173_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(lean_object* v_declName_174_, lean_object* v_e_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_Expr_isConstOf(v_e_175_, v_declName_174_);
return v___x_176_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_174_ = stack[0].m_obj;
lean_object* v_e_175_ = stack[1].m_obj;
uint8_t v_res_177_;
v_res_177_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(v_declName_174_, v_e_175_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed(lean_object* v_declName_178_, lean_object* v_e_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(v_declName_178_, v_e_179_);
lean_dec_ref(v_e_179_);
lean_dec(v_declName_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(lean_object* v_fvarId_182_, lean_object* v_e_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l_Lean_Expr_isFVar(v_e_183_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = l_Lean_Expr_fvarId_x21(v_e_183_);
v___x_186_ = l_Lean_instBEqFVarId_beq(v___x_185_, v_fvarId_182_);
lean_dec(v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_182_ = stack[0].m_obj;
lean_object* v_e_183_ = stack[1].m_obj;
uint8_t v_res_187_;
v_res_187_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(v_fvarId_182_, v_e_183_);
stack->m_num = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed(lean_object* v_fvarId_188_, lean_object* v_e_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(v_fvarId_188_, v_e_189_);
lean_dec_ref(v_e_189_);
lean_dec(v_fvarId_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(lean_object* v_e_192_, lean_object* v_filter_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
switch(lean_obj_tag(v_filter_193_))
{
case 0:
{
uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v_e_192_);
v___x_197_ = 1;
v___x_198_ = lean_box(v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
case 1:
{
lean_object* v_declName_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_221_; 
v_declName_200_ = lean_ctor_get(v_filter_193_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_filter_193_);
if (v_isSharedCheck_221_ == 0)
{
v___x_202_ = v_filter_193_;
v_isShared_203_ = v_isSharedCheck_221_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_declName_200_);
lean_dec(v_filter_193_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_221_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___f_204_; lean_object* v___x_205_; 
v___f_204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_204_, 0, v_declName_200_);
v___x_205_ = lean_find_expr(v___f_204_, v_e_192_);
lean_dec_ref(v_e_192_);
lean_dec_ref(v___f_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = 0;
v___x_207_ = lean_box(v___x_206_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 0);
lean_ctor_set(v___x_202_, 0, v___x_207_);
v___x_209_ = v___x_202_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
else
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_219_; 
lean_del_object(v___x_202_);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_205_, 0);
lean_dec(v_unused_220_);
v___x_212_ = v___x_205_;
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
else
{
lean_dec(v___x_205_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_214_ = 1;
v___x_215_ = lean_box(v___x_214_);
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 0);
lean_ctor_set(v___x_212_, 0, v___x_215_);
v___x_217_ = v___x_212_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
case 2:
{
lean_object* v_fvarId_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_243_; 
v_fvarId_222_ = lean_ctor_get(v_filter_193_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_filter_193_);
if (v_isSharedCheck_243_ == 0)
{
v___x_224_ = v_filter_193_;
v_isShared_225_ = v_isSharedCheck_243_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_fvarId_222_);
lean_dec(v_filter_193_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_243_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___f_226_; lean_object* v___x_227_; 
v___f_226_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_226_, 0, v_fvarId_222_);
v___x_227_ = lean_find_expr(v___f_226_, v_e_192_);
lean_dec_ref(v_e_192_);
lean_dec_ref(v___f_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = 0;
v___x_229_ = lean_box(v___x_228_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 0);
lean_ctor_set(v___x_224_, 0, v___x_229_);
v___x_231_ = v___x_224_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
else
{
lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_241_; 
lean_del_object(v___x_224_);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v___x_227_, 0);
lean_dec(v_unused_242_);
v___x_234_ = v___x_227_;
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
else
{
lean_dec(v___x_227_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = 1;
v___x_237_ = lean_box(v___x_236_);
if (v_isShared_235_ == 0)
{
lean_ctor_set_tag(v___x_234_, 0);
lean_ctor_set(v___x_234_, 0, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
case 3:
{
lean_object* v_pred_244_; lean_object* v___x_245_; 
v_pred_244_ = lean_ctor_get(v_filter_193_, 0);
lean_inc_ref(v_pred_244_);
lean_dec_ref_known(v_filter_193_, 1);
v___x_245_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_192_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_apply_1(v_pred_244_, v_a_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_pred_244_);
v_a_255_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_245_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_245_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
case 4:
{
lean_object* v_a_263_; lean_object* v_b_264_; lean_object* v___x_265_; 
v_a_263_ = lean_ctor_get(v_filter_193_, 0);
lean_inc(v_a_263_);
v_b_264_ = lean_ctor_get(v_filter_193_, 1);
lean_inc(v_b_264_);
lean_dec_ref_known(v_filter_193_, 2);
lean_inc_ref(v_e_192_);
v___x_265_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_192_, v_a_263_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; uint8_t v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v___x_267_ = lean_unbox(v_a_266_);
if (v___x_267_ == 0)
{
lean_dec_ref_known(v___x_265_, 1);
v_filter_193_ = v_b_264_;
goto _start;
}
else
{
lean_dec(v_b_264_);
lean_dec_ref(v_e_192_);
return v___x_265_;
}
}
else
{
lean_dec(v_b_264_);
lean_dec_ref(v_e_192_);
return v___x_265_;
}
}
case 5:
{
lean_object* v_a_269_; lean_object* v_b_270_; lean_object* v___x_271_; 
v_a_269_ = lean_ctor_get(v_filter_193_, 0);
lean_inc(v_a_269_);
v_b_270_ = lean_ctor_get(v_filter_193_, 1);
lean_inc(v_b_270_);
lean_dec_ref_known(v_filter_193_, 2);
lean_inc_ref(v_e_192_);
v___x_271_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_192_, v_a_269_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; uint8_t v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v___x_273_ = lean_unbox(v_a_272_);
if (v___x_273_ == 0)
{
lean_dec(v_b_270_);
lean_dec_ref(v_e_192_);
return v___x_271_;
}
else
{
lean_dec_ref_known(v___x_271_, 1);
v_filter_193_ = v_b_270_;
goto _start;
}
}
else
{
lean_dec(v_b_270_);
lean_dec_ref(v_e_192_);
return v___x_271_;
}
}
default: 
{
lean_object* v_a_275_; lean_object* v___x_276_; 
v_a_275_ = lean_ctor_get(v_filter_193_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v_filter_193_, 1);
v___x_276_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_192_, v_a_275_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_292_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_292_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_292_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_292_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
uint8_t v___x_281_; 
v___x_281_ = lean_unbox(v_a_277_);
lean_dec(v_a_277_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = 1;
v___x_283_ = lean_box(v___x_282_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_283_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
else
{
uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_287_ = 0;
v___x_288_ = lean_box(v___x_287_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_288_);
v___x_290_ = v___x_279_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_192_ = stack[0].m_obj;
lean_object* v_filter_193_ = stack[1].m_obj;
lean_object* v_a_194_ = stack[2].m_obj;
lean_object* v_a_195_ = stack[3].m_obj;
lean_object* v_res_293_;
v_res_293_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_192_, v_filter_193_, v_a_194_, v_a_195_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___boxed(lean_object* v_e_294_, lean_object* v_filter_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_294_, v_filter_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec(v_a_296_);
return v_res_299_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(lean_object* v_e_300_, lean_object* v_filter_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_300_, v_filter_301_, v_a_302_, v_a_309_);
return v___x_313_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_300_ = stack[0].m_obj;
lean_object* v_filter_301_ = stack[1].m_obj;
lean_object* v_a_302_ = stack[2].m_obj;
lean_object* v_a_303_ = stack[3].m_obj;
lean_object* v_a_304_ = stack[4].m_obj;
lean_object* v_a_305_ = stack[5].m_obj;
lean_object* v_a_306_ = stack[6].m_obj;
lean_object* v_a_307_ = stack[7].m_obj;
lean_object* v_a_308_ = stack[8].m_obj;
lean_object* v_a_309_ = stack[9].m_obj;
lean_object* v_a_310_ = stack[10].m_obj;
lean_object* v_a_311_ = stack[11].m_obj;
lean_object* v_res_314_;
v_res_314_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(v_e_300_, v_filter_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___boxed(lean_object* v_e_315_, lean_object* v_filter_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(v_e_315_, v_filter_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec(v_a_317_);
return v_res_328_;
}
}
lean_object* l_Lean_Meta_Grind_Filter_eval___redArg(lean_object* v_filter_329_, lean_object* v_e_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_330_, v_filter_329_, v_a_331_, v_a_332_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Filter_eval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_329_ = stack[0].m_obj;
lean_object* v_e_330_ = stack[1].m_obj;
lean_object* v_a_331_ = stack[2].m_obj;
lean_object* v_a_332_ = stack[3].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Meta_Grind_Filter_eval___redArg(v_filter_329_, v_e_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg___boxed(lean_object* v_filter_336_, lean_object* v_e_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Grind_Filter_eval___redArg(v_filter_336_, v_e_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec(v_a_338_);
return v_res_341_;
}
}
lean_object* l_Lean_Meta_Grind_Filter_eval(lean_object* v_filter_342_, lean_object* v_e_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_343_, v_filter_342_, v_a_344_, v_a_351_);
return v___x_355_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Filter_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_342_ = stack[0].m_obj;
lean_object* v_e_343_ = stack[1].m_obj;
lean_object* v_a_344_ = stack[2].m_obj;
lean_object* v_a_345_ = stack[3].m_obj;
lean_object* v_a_346_ = stack[4].m_obj;
lean_object* v_a_347_ = stack[5].m_obj;
lean_object* v_a_348_ = stack[6].m_obj;
lean_object* v_a_349_ = stack[7].m_obj;
lean_object* v_a_350_ = stack[8].m_obj;
lean_object* v_a_351_ = stack[9].m_obj;
lean_object* v_a_352_ = stack[10].m_obj;
lean_object* v_a_353_ = stack[11].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_Meta_Grind_Filter_eval(v_filter_342_, v_e_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___boxed(lean_object* v_filter_357_, lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Filter_eval(v_filter_357_, v_e_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
}
#ifdef __cplusplus
}
#endif
