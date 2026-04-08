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
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_t_11_);
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
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_94_, v_a_95_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; uint8_t v___x_100_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_unbox(v_a_99_);
lean_dec(v_a_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_94_, v_a_96_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_135_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_135_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_135_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_135_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = l_Lean_Expr_cleanupAnnotations(v_a_102_);
v___x_112_ = l_Lean_Expr_isApp(v___x_111_);
if (v___x_112_ == 0)
{
lean_dec_ref(v___x_111_);
goto v___jp_106_;
}
else
{
lean_object* v_arg_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_arg_113_ = lean_ctor_get(v___x_111_, 1);
lean_inc_ref(v_arg_113_);
v___x_114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_111_);
v___x_115_ = l_Lean_Expr_isApp(v___x_114_);
if (v___x_115_ == 0)
{
lean_dec_ref(v___x_114_);
lean_dec_ref(v_arg_113_);
goto v___jp_106_;
}
else
{
lean_object* v_arg_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_arg_116_ = lean_ctor_get(v___x_114_, 1);
lean_inc_ref(v_arg_116_);
v___x_117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_114_);
v___x_118_ = l_Lean_Expr_isApp(v___x_117_);
if (v___x_118_ == 0)
{
lean_dec_ref(v___x_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_113_);
goto v___jp_106_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_117_);
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1));
v___x_121_ = l_Lean_Expr_isConstOf(v___x_119_, v___x_120_);
lean_dec_ref(v___x_119_);
if (v___x_121_ == 0)
{
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_113_);
goto v___jp_106_;
}
else
{
lean_object* v___x_122_; 
lean_del_object(v___x_104_);
v___x_122_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_116_, v_a_95_);
lean_dec_ref(v_arg_116_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref(v___x_122_);
v___x_124_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_113_, v_a_95_);
lean_dec_ref(v_arg_113_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; uint8_t v___x_126_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
v___x_126_ = lean_nat_dec_le(v_a_123_, v_a_125_);
lean_dec(v_a_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; 
v_unused_134_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_134_);
v___x_128_ = v___x_124_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_dec(v___x_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v_a_123_);
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_123_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_dec(v_a_123_);
return v___x_124_;
}
}
else
{
lean_dec(v_a_123_);
return v___x_124_;
}
}
else
{
lean_dec_ref(v_arg_113_);
return v___x_122_;
}
}
}
}
}
v___jp_106_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(0u);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_101_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_101_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
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
else
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_94_, v_a_95_);
lean_dec_ref(v_e_94_);
return v___x_144_;
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_e_94_);
v_a_145_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_98_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_98_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___boxed(lean_object* v_e_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec(v_a_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(lean_object* v_e_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_158_, v_a_159_, v_a_166_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___boxed(lean_object* v_e_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(v_e_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec(v_a_172_);
return v_res_183_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(lean_object* v_declName_184_, lean_object* v_e_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Expr_isConstOf(v_e_185_, v_declName_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed(lean_object* v_declName_187_, lean_object* v_e_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(v_declName_187_, v_e_188_);
lean_dec_ref(v_e_188_);
lean_dec(v_declName_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(lean_object* v_fvarId_191_, lean_object* v_e_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_Expr_isFVar(v_e_192_);
if (v___x_193_ == 0)
{
return v___x_193_;
}
else
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = l_Lean_Expr_fvarId_x21(v_e_192_);
v___x_195_ = l_Lean_instBEqFVarId_beq(v___x_194_, v_fvarId_191_);
lean_dec(v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed(lean_object* v_fvarId_196_, lean_object* v_e_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(v_fvarId_196_, v_e_197_);
lean_dec_ref(v_e_197_);
lean_dec(v_fvarId_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(lean_object* v_e_200_, lean_object* v_filter_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
switch(lean_obj_tag(v_filter_201_))
{
case 0:
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v_e_200_);
v___x_205_ = 1;
v___x_206_ = lean_box(v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
case 1:
{
lean_object* v_declName_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_229_; 
v_declName_208_ = lean_ctor_get(v_filter_201_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v_filter_201_);
if (v_isSharedCheck_229_ == 0)
{
v___x_210_ = v_filter_201_;
v_isShared_211_ = v_isSharedCheck_229_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_declName_208_);
lean_dec(v_filter_201_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_229_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___f_212_; lean_object* v___x_213_; 
v___f_212_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_212_, 0, v_declName_208_);
v___x_213_ = lean_find_expr(v___f_212_, v_e_200_);
lean_dec_ref(v_e_200_);
lean_dec_ref(v___f_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_214_ = 0;
v___x_215_ = lean_box(v___x_214_);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 0);
lean_ctor_set(v___x_210_, 0, v___x_215_);
v___x_217_ = v___x_210_;
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
else
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_227_; 
lean_del_object(v___x_210_);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v___x_213_, 0);
lean_dec(v_unused_228_);
v___x_220_ = v___x_213_;
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
else
{
lean_dec(v___x_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = 1;
v___x_223_ = lean_box(v___x_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 0);
lean_ctor_set(v___x_220_, 0, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
case 2:
{
lean_object* v_fvarId_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_251_; 
v_fvarId_230_ = lean_ctor_get(v_filter_201_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_filter_201_);
if (v_isSharedCheck_251_ == 0)
{
v___x_232_ = v_filter_201_;
v_isShared_233_ = v_isSharedCheck_251_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_fvarId_230_);
lean_dec(v_filter_201_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_251_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___f_234_; lean_object* v___x_235_; 
v___f_234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_234_, 0, v_fvarId_230_);
v___x_235_ = lean_find_expr(v___f_234_, v_e_200_);
lean_dec_ref(v_e_200_);
lean_dec_ref(v___f_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = 0;
v___x_237_ = lean_box(v___x_236_);
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 0);
lean_ctor_set(v___x_232_, 0, v___x_237_);
v___x_239_ = v___x_232_;
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
else
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_249_; 
lean_del_object(v___x_232_);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v___x_235_, 0);
lean_dec(v_unused_250_);
v___x_242_ = v___x_235_;
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
else
{
lean_dec(v___x_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_244_ = 1;
v___x_245_ = lean_box(v___x_244_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v___x_245_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
case 3:
{
lean_object* v_pred_252_; lean_object* v___x_253_; 
v_pred_252_ = lean_ctor_get(v_filter_201_, 0);
lean_inc_ref(v_pred_252_);
lean_dec_ref(v_filter_201_);
v___x_253_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_200_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_apply_1(v_pred_252_, v_a_254_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_pred_252_);
v_a_263_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_253_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
case 4:
{
lean_object* v_a_271_; lean_object* v_b_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v_filter_201_, 0);
lean_inc(v_a_271_);
v_b_272_ = lean_ctor_get(v_filter_201_, 1);
lean_inc(v_b_272_);
lean_dec_ref(v_filter_201_);
lean_inc_ref(v_e_200_);
v___x_273_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_200_, v_a_271_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; uint8_t v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
v___x_275_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
if (v___x_275_ == 0)
{
lean_dec_ref(v___x_273_);
v_filter_201_ = v_b_272_;
goto _start;
}
else
{
lean_dec(v_b_272_);
lean_dec_ref(v_e_200_);
return v___x_273_;
}
}
else
{
lean_dec(v_b_272_);
lean_dec_ref(v_e_200_);
return v___x_273_;
}
}
case 5:
{
lean_object* v_a_277_; lean_object* v_b_278_; lean_object* v___x_279_; 
v_a_277_ = lean_ctor_get(v_filter_201_, 0);
lean_inc(v_a_277_);
v_b_278_ = lean_ctor_get(v_filter_201_, 1);
lean_inc(v_b_278_);
lean_dec_ref(v_filter_201_);
lean_inc_ref(v_e_200_);
v___x_279_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_200_, v_a_277_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; uint8_t v___x_281_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
v___x_281_ = lean_unbox(v_a_280_);
lean_dec(v_a_280_);
if (v___x_281_ == 0)
{
lean_dec(v_b_278_);
lean_dec_ref(v_e_200_);
return v___x_279_;
}
else
{
lean_dec_ref(v___x_279_);
v_filter_201_ = v_b_278_;
goto _start;
}
}
else
{
lean_dec(v_b_278_);
lean_dec_ref(v_e_200_);
return v___x_279_;
}
}
default: 
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v_filter_201_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v_filter_201_);
v___x_284_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_200_, v_a_283_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_300_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_300_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_300_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_300_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v___x_289_; 
v___x_289_ = lean_unbox(v_a_285_);
lean_dec(v_a_285_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_290_ = 1;
v___x_291_ = lean_box(v___x_290_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_291_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = 0;
v___x_296_ = lean_box(v___x_295_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_296_);
v___x_298_ = v___x_287_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___boxed(lean_object* v_e_301_, lean_object* v_filter_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_301_, v_filter_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec(v_a_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(lean_object* v_e_307_, lean_object* v_filter_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_307_, v_filter_308_, v_a_309_, v_a_316_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___boxed(lean_object* v_e_321_, lean_object* v_filter_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(v_e_321_, v_filter_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg(lean_object* v_filter_335_, lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_336_, v_filter_335_, v_a_337_, v_a_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___redArg___boxed(lean_object* v_filter_341_, lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Grind_Filter_eval___redArg(v_filter_341_, v_e_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec(v_a_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval(lean_object* v_filter_347_, lean_object* v_e_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_348_, v_filter_347_, v_a_349_, v_a_356_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Filter_eval___boxed(lean_object* v_filter_361_, lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Grind_Filter_eval(v_filter_361_, v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_374_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
