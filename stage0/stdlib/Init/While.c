// Lean compiler output
// Module: Init.While
// Imports: public import Init.Core public import Init.Classical public import Init.Control.Ensures public import Init.Control.Lawful.MonadAttach
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
LEAN_EXPORT lean_object* l_whileM_body___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_whileM_body___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_whileM_body(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_body_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_body_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_fix_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_fix_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_fix_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_impl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_impl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_whileM_body___redArg___lam__0(lean_object* v_recur_1_, lean_object* v_toPure_2_, lean_object* v_____do__lift_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_3_) == 0)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
lean_dec(v_toPure_2_);
v_val_4_ = lean_ctor_get(v_____do__lift_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v_____do__lift_3_, 1);
v___x_5_ = lean_apply_1(v_recur_1_, v_val_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_recur_1_);
v_val_6_ = lean_ctor_get(v_____do__lift_3_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_____do__lift_3_, 1);
v___x_7_ = lean_apply_2(v_toPure_2_, lean_box(0), v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_whileM_body___redArg(lean_object* v_inst_8_, lean_object* v_f_9_, lean_object* v_recur_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_toApplicative_12_; lean_object* v_toBind_13_; lean_object* v_toPure_14_; lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_17_; 
v_toApplicative_12_ = lean_ctor_get(v_inst_8_, 0);
lean_inc_ref(v_toApplicative_12_);
v_toBind_13_ = lean_ctor_get(v_inst_8_, 1);
lean_inc(v_toBind_13_);
lean_dec_ref(v_inst_8_);
v_toPure_14_ = lean_ctor_get(v_toApplicative_12_, 1);
lean_inc(v_toPure_14_);
lean_dec_ref(v_toApplicative_12_);
v___x_15_ = lean_apply_1(v_f_9_, v_a_11_);
v___f_16_ = lean_alloc_closure((void*)(l_whileM_body___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_recur_10_);
lean_closure_set(v___f_16_, 1, v_toPure_14_);
v___x_17_ = lean_apply_4(v_toBind_13_, lean_box(0), lean_box(0), v___x_15_, v___f_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_whileM_body(lean_object* v_00_u03b1_18_, lean_object* v_m_19_, lean_object* v_inst_20_, lean_object* v_00_u03b2_21_, lean_object* v_f_22_, lean_object* v_recur_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_toApplicative_25_; lean_object* v_toBind_26_; lean_object* v_toPure_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
v_toApplicative_25_ = lean_ctor_get(v_inst_20_, 0);
lean_inc_ref(v_toApplicative_25_);
v_toBind_26_ = lean_ctor_get(v_inst_20_, 1);
lean_inc(v_toBind_26_);
lean_dec_ref(v_inst_20_);
v_toPure_27_ = lean_ctor_get(v_toApplicative_25_, 1);
lean_inc(v_toPure_27_);
lean_dec_ref(v_toApplicative_25_);
v___x_28_ = lean_apply_1(v_f_22_, v_a_24_);
v___f_29_ = lean_alloc_closure((void*)(l_whileM_body___redArg___lam__0), 3, 2);
lean_closure_set(v___f_29_, 0, v_recur_23_);
lean_closure_set(v___f_29_, 1, v_toPure_27_);
v___x_30_ = lean_apply_4(v_toBind_26_, lean_box(0), lean_box(0), v___x_28_, v___f_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_body_match__1_splitter___redArg(lean_object* v_____do__lift_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (lean_obj_tag(v_____do__lift_31_) == 0)
{
lean_object* v_val_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_33_);
v_val_34_ = lean_ctor_get(v_____do__lift_31_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v_____do__lift_31_, 1);
v___x_35_ = lean_apply_1(v_h__1_32_, v_val_34_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_32_);
v_val_36_ = lean_ctor_get(v_____do__lift_31_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v_____do__lift_31_, 1);
v___x_37_ = lean_apply_1(v_h__2_33_, v_val_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_body_match__1_splitter(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_motive_40_, lean_object* v_____do__lift_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
if (lean_obj_tag(v_____do__lift_41_) == 0)
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_43_);
v_val_44_ = lean_ctor_get(v_____do__lift_41_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v_____do__lift_41_, 1);
v___x_45_ = lean_apply_1(v_h__1_42_, v_val_44_);
return v___x_45_;
}
else
{
lean_object* v_val_46_; lean_object* v___x_47_; 
lean_dec(v_h__1_42_);
v_val_46_ = lean_ctor_get(v_____do__lift_41_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_____do__lift_41_, 1);
v___x_47_ = lean_apply_1(v_h__2_43_, v_val_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_fix_match__1_splitter___redArg(lean_object* v_s_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
if (lean_obj_tag(v_s_48_) == 0)
{
lean_object* v_val_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_50_);
v_val_51_ = lean_ctor_get(v_s_48_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v_s_48_, 1);
v___x_52_ = lean_apply_2(v_h__1_49_, v_val_51_, lean_box(0));
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_49_);
v_val_53_ = lean_ctor_get(v_s_48_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v_s_48_, 1);
v___x_54_ = lean_apply_2(v_h__2_50_, v_val_53_, lean_box(0));
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_fix_match__1_splitter(lean_object* v_00_u03b1_55_, lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_00_u03b2_58_, lean_object* v_f_59_, lean_object* v_x_60_, lean_object* v_motive_61_, lean_object* v_s_62_, lean_object* v_hp_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_s_62_) == 0)
{
lean_object* v_val_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_65_);
v_val_66_ = lean_ctor_get(v_s_62_, 0);
lean_inc(v_val_66_);
lean_dec_ref_known(v_s_62_, 1);
v___x_67_ = lean_apply_2(v_h__1_64_, v_val_66_, lean_box(0));
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; 
lean_dec(v_h__1_64_);
v_val_68_ = lean_ctor_get(v_s_62_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v_s_62_, 1);
v___x_69_ = lean_apply_2(v_h__2_65_, v_val_68_, lean_box(0));
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_fix_match__1_splitter___boxed(lean_object* v_00_u03b1_70_, lean_object* v_m_71_, lean_object* v_inst_72_, lean_object* v_00_u03b2_73_, lean_object* v_f_74_, lean_object* v_x_75_, lean_object* v_motive_76_, lean_object* v_s_77_, lean_object* v_hp_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Init_While_0__whileM_fix_match__1_splitter(v_00_u03b1_70_, v_m_71_, v_inst_72_, v_00_u03b2_73_, v_f_74_, v_x_75_, v_motive_76_, v_s_77_, v_hp_78_, v_h__1_79_, v_h__2_80_);
lean_dec(v_x_75_);
lean_dec(v_f_74_);
lean_dec_ref(v_inst_72_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_impl___redArg(lean_object* v_inst_82_, lean_object* v_f_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_toApplicative_85_; lean_object* v_toBind_86_; lean_object* v_toPure_87_; lean_object* v___x_88_; lean_object* v___f_89_; lean_object* v___x_90_; 
v_toApplicative_85_ = lean_ctor_get(v_inst_82_, 0);
v_toBind_86_ = lean_ctor_get(v_inst_82_, 1);
lean_inc(v_toBind_86_);
v_toPure_87_ = lean_ctor_get(v_toApplicative_85_, 1);
lean_inc(v_toPure_87_);
lean_inc(v_f_83_);
v___x_88_ = lean_apply_1(v_f_83_, v_a_84_);
v___f_89_ = lean_alloc_closure((void*)(l___private_Init_While_0__whileM_impl___redArg___lam__0), 4, 3);
lean_closure_set(v___f_89_, 0, v_inst_82_);
lean_closure_set(v___f_89_, 1, v_f_83_);
lean_closure_set(v___f_89_, 2, v_toPure_87_);
v___x_90_ = lean_apply_4(v_toBind_86_, lean_box(0), lean_box(0), v___x_88_, v___f_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_impl___redArg___lam__0(lean_object* v_inst_91_, lean_object* v_f_92_, lean_object* v_toPure_93_, lean_object* v_____do__lift_94_){
_start:
{
if (lean_obj_tag(v_____do__lift_94_) == 0)
{
lean_object* v_val_95_; lean_object* v___x_96_; 
lean_dec(v_toPure_93_);
v_val_95_ = lean_ctor_get(v_____do__lift_94_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v_____do__lift_94_, 1);
v___x_96_ = l___private_Init_While_0__whileM_impl___redArg(v_inst_91_, v_f_92_, v_val_95_);
return v___x_96_;
}
else
{
lean_object* v_val_97_; lean_object* v___x_98_; 
lean_dec(v_f_92_);
lean_dec_ref(v_inst_91_);
v_val_97_ = lean_ctor_get(v_____do__lift_94_, 0);
lean_inc(v_val_97_);
lean_dec_ref_known(v_____do__lift_94_, 1);
v___x_98_ = lean_apply_2(v_toPure_93_, lean_box(0), v_val_97_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_impl(lean_object* v_00_u03b1_99_, lean_object* v_m_100_, lean_object* v_inst_101_, lean_object* v_00_u03b2_102_, lean_object* v_inst_103_, lean_object* v_f_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l___private_Init_While_0__whileM_impl___redArg(v_inst_101_, v_f_104_, v_a_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___redArg(lean_object* v_inst_107_, lean_object* v_f_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_toApplicative_110_; lean_object* v_toBind_111_; lean_object* v_toPure_112_; lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v_toApplicative_110_ = lean_ctor_get(v_inst_107_, 0);
v_toBind_111_ = lean_ctor_get(v_inst_107_, 1);
lean_inc(v_toBind_111_);
v_toPure_112_ = lean_ctor_get(v_toApplicative_110_, 1);
lean_inc(v_toPure_112_);
lean_inc(v_f_108_);
v___x_113_ = lean_apply_1(v_f_108_, v_a_109_);
v___f_114_ = lean_alloc_closure((void*)(l___private_Init_While_0__whileM_erased___redArg___lam__0), 4, 3);
lean_closure_set(v___f_114_, 0, v_inst_107_);
lean_closure_set(v___f_114_, 1, v_f_108_);
lean_closure_set(v___f_114_, 2, v_toPure_112_);
v___x_115_ = lean_apply_4(v_toBind_111_, lean_box(0), lean_box(0), v___x_113_, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___redArg___lam__0(lean_object* v_inst_116_, lean_object* v_f_117_, lean_object* v_toPure_118_, lean_object* v_____do__lift_119_){
_start:
{
if (lean_obj_tag(v_____do__lift_119_) == 0)
{
lean_object* v_val_120_; lean_object* v___x_121_; 
lean_dec(v_toPure_118_);
v_val_120_ = lean_ctor_get(v_____do__lift_119_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_____do__lift_119_, 1);
v___x_121_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_116_, v_f_117_, v_val_120_);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
lean_dec(v_f_117_);
lean_dec_ref(v_inst_116_);
v_val_122_ = lean_ctor_get(v_____do__lift_119_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v_____do__lift_119_, 1);
v___x_123_ = lean_apply_2(v_toPure_118_, lean_box(0), v_val_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased(lean_object* v_00_u03b1_124_, lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_00_u03b2_127_, lean_object* v_inst_128_, lean_object* v_f_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_126_, v_f_129_, v_a_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object* v_x_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(0u);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__0(lean_object* v_toPure_134_, lean_object* v_____do__lift_135_){
_start:
{
if (lean_obj_tag(v_____do__lift_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_a_136_ = lean_ctor_get(v_____do__lift_135_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v_____do__lift_135_);
if (v_isSharedCheck_144_ == 0)
{
v___x_138_ = v_____do__lift_135_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v_____do__lift_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_141_);
return v___x_142_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
v_a_145_ = lean_ctor_get(v_____do__lift_135_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v_____do__lift_135_);
if (v_isSharedCheck_153_ == 0)
{
v___x_147_ = v_____do__lift_135_;
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v_____do__lift_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 0);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_150_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__1(lean_object* v_f_154_, lean_object* v_toBind_155_, lean_object* v___f_156_, lean_object* v_b_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_2(v_f_154_, v___x_158_, v_b_157_);
v___x_160_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_159_, v___f_156_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object* v_inst_161_, lean_object* v_init_162_, lean_object* v_f_163_){
_start:
{
lean_object* v_toApplicative_164_; lean_object* v_toBind_165_; lean_object* v_toPure_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v_toApplicative_164_ = lean_ctor_get(v_inst_161_, 0);
v_toBind_165_ = lean_ctor_get(v_inst_161_, 1);
v_toPure_166_ = lean_ctor_get(v_toApplicative_164_, 1);
lean_inc(v_toPure_166_);
v___f_167_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_167_, 0, v_toPure_166_);
lean_inc(v_toBind_165_);
v___f_168_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_168_, 0, v_f_163_);
lean_closure_set(v___f_168_, 1, v_toBind_165_);
lean_closure_set(v___f_168_, 2, v___f_167_);
v___x_169_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_161_, v___f_168_, v_init_162_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object* v_00_u03b2_170_, lean_object* v_m_171_, lean_object* v_inst_172_, lean_object* v_x_173_, lean_object* v_init_174_, lean_object* v_f_175_){
_start:
{
lean_object* v_toApplicative_176_; lean_object* v_toBind_177_; lean_object* v_toPure_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v_toApplicative_176_ = lean_ctor_get(v_inst_172_, 0);
v_toBind_177_ = lean_ctor_get(v_inst_172_, 1);
v_toPure_178_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_inc(v_toPure_178_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_179_, 0, v_toPure_178_);
lean_inc(v_toBind_177_);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_180_, 0, v_f_175_);
lean_closure_set(v___f_180_, 1, v_toBind_177_);
lean_closure_set(v___f_180_, 2, v___f_179_);
v___x_181_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_172_, v___f_180_, v_init_174_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(lean_object* v___y_182_, lean_object* v_toBind_183_, lean_object* v___f_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_2(v___y_182_, v___x_186_, v_b_185_);
v___x_188_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_187_, v___f_184_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object* v_inst_189_, lean_object* v_00_u03b2_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_toApplicative_194_; lean_object* v_toBind_195_; lean_object* v_toPure_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_199_; 
v_toApplicative_194_ = lean_ctor_get(v_inst_189_, 0);
v_toBind_195_ = lean_ctor_get(v_inst_189_, 1);
v_toPure_196_ = lean_ctor_get(v_toApplicative_194_, 1);
lean_inc(v_toPure_196_);
v___f_197_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_197_, 0, v_toPure_196_);
lean_inc(v_toBind_195_);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_198_, 0, v___y_193_);
lean_closure_set(v___f_198_, 1, v_toBind_195_);
lean_closure_set(v___f_198_, 2, v___f_197_);
v___x_199_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_189_, v___f_198_, v___y_192_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object* v_inst_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_201_, 0, v_inst_200_);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object* v_m_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___f_204_; 
v___f_204_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_204_, 0, v_inst_203_);
return v___f_204_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Ensures(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_MonadAttach(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Ensures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_MonadAttach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Control_Ensures(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful_MonadAttach(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Ensures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful_MonadAttach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_While(builtin);
}
#ifdef __cplusplus
}
#endif
