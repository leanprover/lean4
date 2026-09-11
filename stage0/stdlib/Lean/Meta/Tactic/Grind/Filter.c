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
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx(lean_object* v_x_1_){
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
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Grind_Filter_ctorIdx(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 0:
{
return v_k_12_;
}
case 3:
{
lean_object* v_pred_13_; lean_object* v___x_14_; 
v_pred_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_pred_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_pred_13_);
return v___x_14_;
}
case 4:
{
lean_object* v_a_15_; lean_object* v_b_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
v_b_16_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_b_16_);
lean_dec_ref_known(v_t_11_, 2);
v___x_17_ = lean_apply_2(v_k_12_, v_a_15_, v_b_16_);
return v___x_17_;
}
case 5:
{
lean_object* v_a_18_; lean_object* v_b_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_18_);
v_b_19_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_b_19_);
lean_dec_ref_known(v_t_11_, 2);
v___x_20_ = lean_apply_2(v_k_12_, v_a_18_, v_b_19_);
return v___x_20_;
}
default: 
{
lean_object* v_declName_21_; lean_object* v___x_22_; 
v_declName_21_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_declName_21_);
lean_dec(v_t_11_);
v___x_22_ = lean_apply_1(v_k_12_, v_declName_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_25_, v_k_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_ctorElim___boxed(lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_Grind_Filter_ctorElim(v_motive_29_, v_ctorIdx_30_, v_t_31_, v_h_32_, v_k_33_);
lean_dec(v_ctorIdx_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_true_elim___redArg(lean_object* v_t_35_, lean_object* v_true_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_35_, v_true_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_true_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_true_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_39_, v_true_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_const_elim___redArg(lean_object* v_t_43_, lean_object* v_const_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_43_, v_const_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_const_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_const_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_47_, v_const_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_fvar_elim___redArg(lean_object* v_t_51_, lean_object* v_fvar_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_51_, v_fvar_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_fvar_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_fvar_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_55_, v_fvar_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_gen_elim___redArg(lean_object* v_t_59_, lean_object* v_gen_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_59_, v_gen_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_gen_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_gen_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_63_, v_gen_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_or_elim___redArg(lean_object* v_t_67_, lean_object* v_or_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_67_, v_or_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_or_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_or_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_71_, v_or_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_and_elim___redArg(lean_object* v_t_75_, lean_object* v_and_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_75_, v_and_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_and_elim(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_and_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_79_, v_and_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_not_elim___redArg(lean_object* v_t_83_, lean_object* v_not_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_83_, v_not_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_not_elim(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_not_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_87_, v_not_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(lean_object* v_e_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_94_, v_a_95_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; uint8_t v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = lean_unbox(v_a_102_);
lean_dec(v_a_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_94_, v_a_96_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = l_Lean_Expr_cleanupAnnotations(v_a_105_);
v___x_107_ = l_Lean_Expr_isApp(v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v___x_106_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_arg_108_ = lean_ctor_get(v___x_106_, 1);
lean_inc_ref(v_arg_108_);
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_106_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v___x_109_);
lean_dec_ref(v_arg_108_);
goto v___jp_98_;
}
else
{
lean_object* v_arg_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_arg_111_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_111_);
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_113_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_113_ == 0)
{
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_108_);
goto v___jp_98_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1));
v___x_116_ = l_Lean_Expr_isConstOf(v___x_114_, v___x_115_);
lean_dec_ref(v___x_114_);
if (v___x_116_ == 0)
{
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_108_);
goto v___jp_98_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_111_, v_a_95_);
lean_dec_ref(v_arg_111_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_119_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v___x_119_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_108_, v_a_95_);
lean_dec_ref(v_arg_108_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; uint8_t v___x_121_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
v___x_121_ = lean_nat_dec_le(v_a_118_, v_a_120_);
lean_dec(v_a_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_119_, 0);
lean_dec(v_unused_129_);
v___x_123_ = v___x_119_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_dec(v___x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v_a_118_);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_118_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_dec(v_a_118_);
return v___x_119_;
}
}
else
{
lean_dec(v_a_118_);
return v___x_119_;
}
}
else
{
lean_dec_ref(v_arg_108_);
return v___x_117_;
}
}
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_104_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_104_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_94_, v_a_95_);
lean_dec_ref(v_e_94_);
return v___x_138_;
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec_ref(v_e_94_);
v_a_139_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_101_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_101_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
v___jp_98_:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___boxed(lean_object* v_e_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec(v_a_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(lean_object* v_e_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_152_, v_a_153_, v_a_160_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___boxed(lean_object* v_e_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(v_e_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec(v_a_166_);
return v_res_177_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(lean_object* v_declName_178_, lean_object* v_e_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = l_Lean_Expr_isConstOf(v_e_179_, v_declName_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed(lean_object* v_declName_181_, lean_object* v_e_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(v_declName_181_, v_e_182_);
lean_dec_ref(v_e_182_);
lean_dec(v_declName_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(lean_object* v_fvarId_185_, lean_object* v_e_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Lean_Expr_isFVar(v_e_186_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = l_Lean_Expr_fvarId_x21(v_e_186_);
v___x_189_ = l_Lean_instBEqFVarId_beq(v___x_188_, v_fvarId_185_);
lean_dec(v___x_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed(lean_object* v_fvarId_190_, lean_object* v_e_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(v_fvarId_190_, v_e_191_);
lean_dec_ref(v_e_191_);
lean_dec(v_fvarId_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(lean_object* v_e_194_, lean_object* v_filter_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
switch(lean_obj_tag(v_filter_195_))
{
case 0:
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref(v_e_194_);
v___x_199_ = 1;
v___x_200_ = lean_box(v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
case 1:
{
lean_object* v_declName_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_223_; 
v_declName_202_ = lean_ctor_get(v_filter_195_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_filter_195_);
if (v_isSharedCheck_223_ == 0)
{
v___x_204_ = v_filter_195_;
v_isShared_205_ = v_isSharedCheck_223_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_declName_202_);
lean_dec(v_filter_195_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_223_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___f_206_; lean_object* v___x_207_; 
v___f_206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_206_, 0, v_declName_202_);
v___x_207_ = lean_find_expr(v___f_206_, v_e_194_);
lean_dec_ref(v_e_194_);
lean_dec_ref(v___f_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = 0;
v___x_209_ = lean_box(v___x_208_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 0);
lean_ctor_set(v___x_204_, 0, v___x_209_);
v___x_211_ = v___x_204_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
lean_del_object(v___x_204_);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v___x_207_, 0);
lean_dec(v_unused_222_);
v___x_214_ = v___x_207_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_dec(v___x_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = 1;
v___x_217_ = lean_box(v___x_216_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 0);
lean_ctor_set(v___x_214_, 0, v___x_217_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
case 2:
{
lean_object* v_fvarId_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_245_; 
v_fvarId_224_ = lean_ctor_get(v_filter_195_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_filter_195_);
if (v_isSharedCheck_245_ == 0)
{
v___x_226_ = v_filter_195_;
v_isShared_227_ = v_isSharedCheck_245_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_fvarId_224_);
lean_dec(v_filter_195_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_245_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___f_228_; lean_object* v___x_229_; 
v___f_228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_228_, 0, v_fvarId_224_);
v___x_229_ = lean_find_expr(v___f_228_, v_e_194_);
lean_dec_ref(v_e_194_);
lean_dec_ref(v___f_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = 0;
v___x_231_ = lean_box(v___x_230_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 0);
lean_ctor_set(v___x_226_, 0, v___x_231_);
v___x_233_ = v___x_226_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_243_; 
lean_del_object(v___x_226_);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v___x_229_, 0);
lean_dec(v_unused_244_);
v___x_236_ = v___x_229_;
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_229_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_238_ = 1;
v___x_239_ = lean_box(v___x_238_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 0);
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
case 3:
{
lean_object* v_pred_246_; lean_object* v___x_247_; 
v_pred_246_ = lean_ctor_get(v_filter_195_, 0);
lean_inc_ref(v_pred_246_);
lean_dec_ref_known(v_filter_195_, 1);
v___x_247_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_194_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_apply_1(v_pred_246_, v_a_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_pred_246_);
v_a_257_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_247_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_247_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
case 4:
{
lean_object* v_a_265_; lean_object* v_b_266_; lean_object* v___x_267_; 
v_a_265_ = lean_ctor_get(v_filter_195_, 0);
lean_inc(v_a_265_);
v_b_266_ = lean_ctor_get(v_filter_195_, 1);
lean_inc(v_b_266_);
lean_dec_ref_known(v_filter_195_, 2);
lean_inc_ref(v_e_194_);
v___x_267_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_194_, v_a_265_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; uint8_t v___x_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
v___x_269_ = lean_unbox(v_a_268_);
lean_dec(v_a_268_);
if (v___x_269_ == 0)
{
lean_dec_ref_known(v___x_267_, 1);
v_filter_195_ = v_b_266_;
goto _start;
}
else
{
lean_dec(v_b_266_);
lean_dec_ref(v_e_194_);
return v___x_267_;
}
}
else
{
lean_dec(v_b_266_);
lean_dec_ref(v_e_194_);
return v___x_267_;
}
}
case 5:
{
lean_object* v_a_271_; lean_object* v_b_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v_filter_195_, 0);
lean_inc(v_a_271_);
v_b_272_ = lean_ctor_get(v_filter_195_, 1);
lean_inc(v_b_272_);
lean_dec_ref_known(v_filter_195_, 2);
lean_inc_ref(v_e_194_);
v___x_273_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_194_, v_a_271_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; uint8_t v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
v___x_275_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
if (v___x_275_ == 0)
{
lean_dec(v_b_272_);
lean_dec_ref(v_e_194_);
return v___x_273_;
}
else
{
lean_dec_ref_known(v___x_273_, 1);
v_filter_195_ = v_b_272_;
goto _start;
}
}
else
{
lean_dec(v_b_272_);
lean_dec_ref(v_e_194_);
return v___x_273_;
}
}
default: 
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v_filter_195_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v_filter_195_, 1);
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_194_, v_a_277_, v_a_196_, v_a_197_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_294_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_294_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_294_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = lean_unbox(v_a_279_);
lean_dec(v_a_279_);
if (v___x_283_ == 0)
{
uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_284_ = 1;
v___x_285_ = lean_box(v___x_284_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_285_);
v___x_287_ = v___x_281_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_289_ = 0;
v___x_290_ = lean_box(v___x_289_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_290_);
v___x_292_ = v___x_281_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___boxed(lean_object* v_e_295_, lean_object* v_filter_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_295_, v_filter_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(lean_object* v_e_301_, lean_object* v_filter_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_301_, v_filter_302_, v_a_303_, v_a_310_);
return v___x_314_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg(lean_object* v_filter_329_, lean_object* v_e_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_330_, v_filter_329_, v_a_331_, v_a_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg___boxed(lean_object* v_filter_335_, lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_Grind_Filter_eval___redArg(v_filter_335_, v_e_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec(v_a_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval(lean_object* v_filter_341_, lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_342_, v_filter_341_, v_a_343_, v_a_350_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___boxed(lean_object* v_filter_355_, lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Grind_Filter_eval(v_filter_355_, v_e_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec(v_a_357_);
return v_res_368_;
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
