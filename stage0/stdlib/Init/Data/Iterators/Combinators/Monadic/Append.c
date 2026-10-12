// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Append
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Classical import Init.Data.Option.Lemmas import Init.ByCases import Init.Omega
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_fst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_fst_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_snd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_snd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Iterators_Types_Append_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl(lean_object* v_00_u03b1_u2081_5_, lean_object* v_00_u03b1_u2082_6_, lean_object* v_m_7_, lean_object* v_00_u03b2_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_tag_nat(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___impl___boxed(lean_object* v_00_u03b1_u2081_11_, lean_object* v_00_u03b1_u2082_12_, lean_object* v_m_13_, lean_object* v_00_u03b2_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Iterators_Types_Append_ctorIdx___impl(v_00_u03b1_u2081_11_, v_00_u03b1_u2082_12_, v_m_13_, v_00_u03b2_14_, v_x_15_);
lean_dec_ref(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim___redArg(lean_object* v_t_17_, lean_object* v_k_18_){
_start:
{
if (lean_obj_tag(v_t_17_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_a_19_);
v_a_20_ = lean_ctor_get(v_t_17_, 1);
lean_inc(v_a_20_);
lean_dec_ref_known(v_t_17_, 2);
v___x_21_ = lean_apply_2(v_k_18_, v_a_19_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_22_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v_t_17_, 1);
v___x_23_ = lean_apply_1(v_k_18_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim(lean_object* v_00_u03b1_u2081_24_, lean_object* v_00_u03b1_u2082_25_, lean_object* v_m_26_, lean_object* v_00_u03b2_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_30_, v_k_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim___boxed(lean_object* v_00_u03b1_u2081_34_, lean_object* v_00_u03b1_u2082_35_, lean_object* v_m_36_, lean_object* v_00_u03b2_37_, lean_object* v_motive_38_, lean_object* v_ctorIdx_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Iterators_Types_Append_ctorElim(v_00_u03b1_u2081_34_, v_00_u03b1_u2082_35_, v_m_36_, v_00_u03b2_37_, v_motive_38_, v_ctorIdx_39_, v_t_40_, v_h_41_, v_k_42_);
lean_dec(v_ctorIdx_39_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_fst_elim___redArg(lean_object* v_t_44_, lean_object* v_fst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_44_, v_fst_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_fst_elim(lean_object* v_00_u03b1_u2081_47_, lean_object* v_00_u03b1_u2082_48_, lean_object* v_m_49_, lean_object* v_00_u03b2_50_, lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_fst_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_52_, v_fst_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_snd_elim___redArg(lean_object* v_t_56_, lean_object* v_snd_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_56_, v_snd_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_snd_elim(lean_object* v_00_u03b1_u2081_59_, lean_object* v_00_u03b1_u2082_60_, lean_object* v_m_61_, lean_object* v_00_u03b2_62_, lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_snd_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_64_, v_snd_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_append___redArg(lean_object* v_it_u2081_68_, lean_object* v_it_u2082_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_it_u2081_68_);
lean_ctor_set(v___x_70_, 1, v_it_u2082_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_append(lean_object* v_m_71_, lean_object* v_00_u03b2_72_, lean_object* v_00_u03b1_u2081_73_, lean_object* v_00_u03b1_u2082_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_it_u2081_77_, lean_object* v_it_u2082_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v_it_u2081_77_);
lean_ctor_set(v___x_79_, 1, v_it_u2082_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_append___boxed(lean_object* v_m_80_, lean_object* v_00_u03b2_81_, lean_object* v_00_u03b1_u2081_82_, lean_object* v_00_u03b1_u2082_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_it_u2081_86_, lean_object* v_it_u2082_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_IterM_append(v_m_80_, v_00_u03b2_81_, v_00_u03b1_u2081_82_, v_00_u03b1_u2082_83_, v_inst_84_, v_inst_85_, v_it_u2081_86_, v_it_u2082_87_);
lean_dec(v_inst_85_);
lean_dec(v_inst_84_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd___redArg(lean_object* v_it_u2082_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v_it_u2082_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd(lean_object* v_m_91_, lean_object* v_00_u03b2_92_, lean_object* v_00_u03b1_u2082_93_, lean_object* v_inst_94_, lean_object* v_00_u03b1_u2081_95_, lean_object* v_it_u2082_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_it_u2082_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd___boxed(lean_object* v_m_98_, lean_object* v_00_u03b2_99_, lean_object* v_00_u03b1_u2082_100_, lean_object* v_inst_101_, lean_object* v_00_u03b1_u2081_102_, lean_object* v_it_u2082_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_IterM_Intermediate_appendSnd(v_m_98_, v_00_u03b2_99_, v_00_u03b1_u2082_100_, v_inst_101_, v_00_u03b1_u2081_102_, v_it_u2082_103_);
lean_dec(v_inst_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__0(lean_object* v_toPure_105_, lean_object* v_____do__lift_106_){
_start:
{
switch(lean_obj_tag(v_____do__lift_106_))
{
case 0:
{
lean_object* v_it_107_; lean_object* v_out_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_117_; 
v_it_107_ = lean_ctor_get(v_____do__lift_106_, 0);
v_out_108_ = lean_ctor_get(v_____do__lift_106_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_____do__lift_106_);
if (v_isSharedCheck_117_ == 0)
{
v___x_110_ = v_____do__lift_106_;
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_out_108_);
lean_inc(v_it_107_);
lean_dec(v_____do__lift_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_it_107_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_out_108_);
v___x_114_ = v_reuseFailAlloc_116_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; 
v___x_115_ = lean_apply_2(v_toPure_105_, lean_box(0), v___x_114_);
return v___x_115_;
}
}
}
case 1:
{
lean_object* v_it_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_127_; 
v_it_118_ = lean_ctor_get(v_____do__lift_106_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_____do__lift_106_);
if (v_isSharedCheck_127_ == 0)
{
v___x_120_ = v_____do__lift_106_;
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_it_118_);
lean_dec(v_____do__lift_106_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_it_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_126_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; 
v___x_125_ = lean_apply_2(v_toPure_105_, lean_box(0), v___x_124_);
return v___x_125_;
}
}
}
default: 
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_box(2);
v___x_129_ = lean_apply_2(v_toPure_105_, lean_box(0), v___x_128_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__1(lean_object* v_a_130_, lean_object* v_toPure_131_, lean_object* v_____do__lift_132_){
_start:
{
switch(lean_obj_tag(v_____do__lift_132_))
{
case 0:
{
lean_object* v_it_133_; lean_object* v_out_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_143_; 
v_it_133_ = lean_ctor_get(v_____do__lift_132_, 0);
v_out_134_ = lean_ctor_get(v_____do__lift_132_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_____do__lift_132_);
if (v_isSharedCheck_143_ == 0)
{
v___x_136_ = v_____do__lift_132_;
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_out_134_);
lean_inc(v_it_133_);
lean_dec(v_____do__lift_132_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_it_133_);
lean_ctor_set(v___x_138_, 1, v_a_130_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_out_134_);
v___x_140_ = v_reuseFailAlloc_142_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
v___x_141_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_140_);
return v___x_141_;
}
}
}
case 1:
{
lean_object* v_it_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v_it_144_ = lean_ctor_get(v_____do__lift_132_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v_____do__lift_132_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v_____do__lift_132_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_it_144_);
lean_dec(v_____do__lift_132_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v_it_144_);
lean_ctor_set(v___x_148_, 1, v_a_130_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_150_);
return v___x_151_;
}
}
}
default: 
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v_a_130_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
v___x_156_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__2(lean_object* v_toPure_157_, lean_object* v_inst_158_, lean_object* v_toBind_159_, lean_object* v_inst_160_, lean_object* v___f_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v_a_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___f_161_);
lean_dec(v_inst_160_);
v_a_163_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_a_163_);
v_a_164_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_a_164_);
lean_dec_ref_known(v_x_162_, 2);
v___f_165_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_165_, 0, v_a_164_);
lean_closure_set(v___f_165_, 1, v_toPure_157_);
v___x_166_ = lean_apply_1(v_inst_158_, v_a_163_);
v___x_167_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_166_, v___f_165_);
return v___x_167_;
}
else
{
lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_inst_158_);
lean_dec(v_toPure_157_);
v_a_168_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v_x_162_, 1);
v___x_169_ = lean_apply_1(v_inst_160_, v_a_168_);
v___x_170_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_169_, v___f_161_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_){
_start:
{
lean_object* v_toApplicative_174_; lean_object* v_toBind_175_; lean_object* v_toPure_176_; lean_object* v___f_177_; lean_object* v___f_178_; 
v_toApplicative_174_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_ref(v_toApplicative_174_);
v_toBind_175_ = lean_ctor_get(v_inst_171_, 1);
lean_inc(v_toBind_175_);
lean_dec_ref(v_inst_171_);
v_toPure_176_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc_n(v_toPure_176_, 2);
lean_dec_ref(v_toApplicative_174_);
v___f_177_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_177_, 0, v_toPure_176_);
v___f_178_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__2), 6, 5);
lean_closure_set(v___f_178_, 0, v_toPure_176_);
lean_closure_set(v___f_178_, 1, v_inst_172_);
lean_closure_set(v___f_178_, 2, v_toBind_175_);
lean_closure_set(v___f_178_, 3, v_inst_173_);
lean_closure_set(v___f_178_, 4, v___f_177_);
return v___f_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator(lean_object* v_m_179_, lean_object* v_00_u03b2_180_, lean_object* v_00_u03b1_u2081_181_, lean_object* v_00_u03b1_u2082_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v_toApplicative_186_; lean_object* v_toBind_187_; lean_object* v_toPure_188_; lean_object* v___f_189_; lean_object* v___f_190_; 
v_toApplicative_186_ = lean_ctor_get(v_inst_183_, 0);
lean_inc_ref(v_toApplicative_186_);
v_toBind_187_ = lean_ctor_get(v_inst_183_, 1);
lean_inc(v_toBind_187_);
lean_dec_ref(v_inst_183_);
v_toPure_188_ = lean_ctor_get(v_toApplicative_186_, 1);
lean_inc_n(v_toPure_188_, 2);
lean_dec_ref(v_toApplicative_186_);
v___f_189_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_189_, 0, v_toPure_188_);
v___f_190_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__2), 6, 5);
lean_closure_set(v___f_190_, 0, v_toPure_188_);
lean_closure_set(v___f_190_, 1, v_inst_184_);
lean_closure_set(v___f_190_, 2, v_toBind_187_);
lean_closure_set(v___f_190_, 3, v_inst_185_);
lean_closure_set(v___f_190_, 4, v___f_189_);
return v___f_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_191_, lean_object* v_recur_192_, lean_object* v_it_193_, lean_object* v_____do__lift_194_){
_start:
{
if (lean_obj_tag(v_____do__lift_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; 
lean_dec_ref(v_it_193_);
lean_dec(v_recur_192_);
v_a_195_ = lean_ctor_get(v_____do__lift_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v_____do__lift_194_, 1);
v___x_196_ = lean_apply_2(v_toPure_191_, lean_box(0), v_a_195_);
return v___x_196_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_198_; 
lean_dec(v_toPure_191_);
v_a_197_ = lean_ctor_get(v_____do__lift_194_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v_____do__lift_194_, 1);
v___x_198_ = lean_apply_4(v_recur_192_, v_it_193_, v_a_197_, lean_box(0), lean_box(0));
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_199_, lean_object* v_recur_200_, lean_object* v___y_201_, lean_object* v_acc_202_, lean_object* v_toBind_203_, lean_object* v_s_204_){
_start:
{
switch(lean_obj_tag(v_s_204_))
{
case 0:
{
lean_object* v_it_205_; lean_object* v_out_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_it_205_ = lean_ctor_get(v_s_204_, 0);
lean_inc(v_it_205_);
v_out_206_ = lean_ctor_get(v_s_204_, 1);
lean_inc(v_out_206_);
lean_dec_ref_known(v_s_204_, 2);
v___f_207_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_207_, 0, v_toPure_199_);
lean_closure_set(v___f_207_, 1, v_recur_200_);
lean_closure_set(v___f_207_, 2, v_it_205_);
v___x_208_ = lean_apply_3(v___y_201_, v_out_206_, lean_box(0), v_acc_202_);
v___x_209_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v___x_208_, v___f_207_);
return v___x_209_;
}
case 1:
{
lean_object* v_it_210_; lean_object* v___x_211_; 
lean_dec(v_toBind_203_);
lean_dec(v___y_201_);
lean_dec(v_toPure_199_);
v_it_210_ = lean_ctor_get(v_s_204_, 0);
lean_inc(v_it_210_);
lean_dec_ref_known(v_s_204_, 1);
v___x_211_ = lean_apply_4(v_recur_200_, v_it_210_, v_acc_202_, lean_box(0), lean_box(0));
return v___x_211_;
}
default: 
{
lean_object* v___x_212_; 
lean_dec(v_toBind_203_);
lean_dec(v___y_201_);
lean_dec(v_recur_200_);
v___x_212_ = lean_apply_2(v_toPure_199_, lean_box(0), v_acc_202_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4(lean_object* v_inst_213_, lean_object* v_toPure_214_, lean_object* v___y_215_, lean_object* v_toBind_216_, lean_object* v_inst_217_, lean_object* v_lift_218_, lean_object* v_inst_219_, lean_object* v_it_220_, lean_object* v_acc_221_, lean_object* v_hP_222_, lean_object* v_recur_223_){
_start:
{
lean_object* v_toApplicative_224_; lean_object* v_toBind_225_; lean_object* v_toPure_226_; lean_object* v___f_227_; 
v_toApplicative_224_ = lean_ctor_get(v_inst_213_, 0);
lean_inc_ref(v_toApplicative_224_);
v_toBind_225_ = lean_ctor_get(v_inst_213_, 1);
lean_inc(v_toBind_225_);
lean_dec_ref(v_inst_213_);
v_toPure_226_ = lean_ctor_get(v_toApplicative_224_, 1);
lean_inc(v_toPure_226_);
lean_dec_ref(v_toApplicative_224_);
v___f_227_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_227_, 0, v_toPure_214_);
lean_closure_set(v___f_227_, 1, v_recur_223_);
lean_closure_set(v___f_227_, 2, v___y_215_);
lean_closure_set(v___f_227_, 3, v_acc_221_);
lean_closure_set(v___f_227_, 4, v_toBind_216_);
if (lean_obj_tag(v_it_220_) == 0)
{
lean_object* v_a_228_; lean_object* v_a_229_; lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_inst_219_);
v_a_228_ = lean_ctor_get(v_it_220_, 0);
lean_inc(v_a_228_);
v_a_229_ = lean_ctor_get(v_it_220_, 1);
lean_inc(v_a_229_);
lean_dec_ref_known(v_it_220_, 2);
v___f_230_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_230_, 0, v_a_229_);
lean_closure_set(v___f_230_, 1, v_toPure_226_);
v___x_231_ = lean_apply_1(v_inst_217_, v_a_228_);
v___x_232_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v___x_231_, v___f_230_);
v___x_233_ = lean_apply_4(v_lift_218_, lean_box(0), lean_box(0), v___f_227_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_a_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_inst_217_);
v_a_234_ = lean_ctor_get(v_it_220_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v_it_220_, 1);
v___f_235_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_235_, 0, v_toPure_226_);
v___x_236_ = lean_apply_1(v_inst_219_, v_a_234_);
v___x_237_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v___x_236_, v___f_235_);
v___x_238_ = lean_apply_4(v_lift_218_, lean_box(0), lean_box(0), v___f_227_, v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_lift_243_, lean_object* v_00_u03b3_244_, lean_object* v_Pl_245_, lean_object* v_it_246_, lean_object* v_init_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_toApplicative_249_; lean_object* v_toBind_250_; lean_object* v_toPure_251_; lean_object* v___f_252_; lean_object* v___x_253_; 
v_toApplicative_249_ = lean_ctor_get(v_inst_239_, 0);
lean_inc_ref(v_toApplicative_249_);
v_toBind_250_ = lean_ctor_get(v_inst_239_, 1);
lean_inc(v_toBind_250_);
lean_dec_ref(v_inst_239_);
v_toPure_251_ = lean_ctor_get(v_toApplicative_249_, 1);
lean_inc(v_toPure_251_);
lean_dec_ref(v_toApplicative_249_);
v___f_252_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_252_, 0, v_inst_240_);
lean_closure_set(v___f_252_, 1, v_toPure_251_);
lean_closure_set(v___f_252_, 2, v___y_248_);
lean_closure_set(v___f_252_, 3, v_toBind_250_);
lean_closure_set(v___f_252_, 4, v_inst_241_);
lean_closure_set(v___f_252_, 5, v_lift_243_);
lean_closure_set(v___f_252_, 6, v_inst_242_);
v___x_253_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_252_, v_it_246_, v_init_247_, lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_){
_start:
{
lean_object* v___f_258_; 
v___f_258_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_258_, 0, v_inst_255_);
lean_closure_set(v___f_258_, 1, v_inst_254_);
lean_closure_set(v___f_258_, 2, v_inst_256_);
lean_closure_set(v___f_258_, 3, v_inst_257_);
return v___f_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop(lean_object* v_m_259_, lean_object* v_00_u03b2_260_, lean_object* v_00_u03b1_u2081_261_, lean_object* v_00_u03b1_u2082_262_, lean_object* v_n_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___f_268_; 
v___f_268_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_268_, 0, v_inst_265_);
lean_closure_set(v___f_268_, 1, v_inst_264_);
lean_closure_set(v___f_268_, 2, v_inst_266_);
lean_closure_set(v___f_268_, 3, v_inst_267_);
return v___f_268_;
}
}
lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
}
LEAN_EXPORT void l_Std_Iterators_Types_Append_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_271_;
v_res_271_ = l_Std_Iterators_Types_Append_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Iterators_Types_Append_instFinitenessRelation___redArg();
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation(lean_object* v_00_u03b1_u2081_274_, lean_object* v_00_u03b1_u2082_275_, lean_object* v_m_276_, lean_object* v_00_u03b2_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(lean_object* v_00_u03b1_u2081_284_, lean_object* v_00_u03b1_u2082_285_, lean_object* v_m_286_, lean_object* v_00_u03b2_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Iterators_Types_Append_instFinitenessRelation(v_00_u03b1_u2081_284_, v_00_u03b1_u2082_285_, v_m_286_, v_00_u03b2_287_, v_inst_288_, v_inst_289_, v_inst_290_, v_inst_291_, v_inst_292_);
lean_dec(v_inst_290_);
lean_dec(v_inst_289_);
lean_dec_ref(v_inst_288_);
return v_res_293_;
}
}
lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_296_;
v_res_296_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___redArg();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(lean_object* v_00_u03b1_u2081_299_, lean_object* v_00_u03b1_u2082_300_, lean_object* v_m_301_, lean_object* v_00_u03b2_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_box(0);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(lean_object* v_00_u03b1_u2081_309_, lean_object* v_00_u03b1_u2082_310_, lean_object* v_m_311_, lean_object* v_00_u03b2_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(v_00_u03b1_u2081_309_, v_00_u03b1_u2082_310_, v_m_311_, v_00_u03b2_312_, v_inst_313_, v_inst_314_, v_inst_315_, v_inst_316_, v_inst_317_);
lean_dec(v_inst_315_);
lean_dec(v_inst_314_);
lean_dec_ref(v_inst_313_);
return v_res_318_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
}
#ifdef __cplusplus
}
#endif
