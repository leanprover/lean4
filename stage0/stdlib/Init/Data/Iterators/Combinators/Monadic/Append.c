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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx(lean_object* v_00_u03b1_u2081_6_, lean_object* v_00_u03b1_u2082_7_, lean_object* v_m_8_, lean_object* v_00_u03b2_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorIdx___boxed(lean_object* v_00_u03b1_u2081_12_, lean_object* v_00_u03b1_u2082_13_, lean_object* v_m_14_, lean_object* v_00_u03b2_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_Iterators_Types_Append_ctorIdx(v_00_u03b1_u2081_12_, v_00_u03b1_u2082_13_, v_m_14_, v_00_u03b2_15_, v_x_16_);
lean_dec_ref(v_x_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim___redArg(lean_object* v_t_18_, lean_object* v_k_19_){
_start:
{
if (lean_obj_tag(v_t_18_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; 
v_a_20_ = lean_ctor_get(v_t_18_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v_t_18_, 1);
lean_inc(v_a_21_);
lean_dec_ref(v_t_18_);
v___x_22_ = lean_apply_2(v_k_19_, v_a_20_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_23_ = lean_ctor_get(v_t_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref(v_t_18_);
v___x_24_ = lean_apply_1(v_k_19_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim(lean_object* v_00_u03b1_u2081_25_, lean_object* v_00_u03b1_u2082_26_, lean_object* v_m_27_, lean_object* v_00_u03b2_28_, lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_31_, v_k_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_ctorElim___boxed(lean_object* v_00_u03b1_u2081_35_, lean_object* v_00_u03b1_u2082_36_, lean_object* v_m_37_, lean_object* v_00_u03b2_38_, lean_object* v_motive_39_, lean_object* v_ctorIdx_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_k_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Iterators_Types_Append_ctorElim(v_00_u03b1_u2081_35_, v_00_u03b1_u2082_36_, v_m_37_, v_00_u03b2_38_, v_motive_39_, v_ctorIdx_40_, v_t_41_, v_h_42_, v_k_43_);
lean_dec(v_ctorIdx_40_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_fst_elim___redArg(lean_object* v_t_45_, lean_object* v_fst_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_45_, v_fst_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_fst_elim(lean_object* v_00_u03b1_u2081_48_, lean_object* v_00_u03b1_u2082_49_, lean_object* v_m_50_, lean_object* v_00_u03b2_51_, lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_fst_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_53_, v_fst_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_snd_elim___redArg(lean_object* v_t_57_, lean_object* v_snd_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_57_, v_snd_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_snd_elim(lean_object* v_00_u03b1_u2081_60_, lean_object* v_00_u03b1_u2082_61_, lean_object* v_m_62_, lean_object* v_00_u03b2_63_, lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_snd_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_65_, v_snd_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_append___redArg(lean_object* v_it_u2081_69_, lean_object* v_it_u2082_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_it_u2081_69_);
lean_ctor_set(v___x_71_, 1, v_it_u2082_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_append(lean_object* v_m_72_, lean_object* v_00_u03b2_73_, lean_object* v_00_u03b1_u2081_74_, lean_object* v_00_u03b1_u2082_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_it_u2081_78_, lean_object* v_it_u2082_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_it_u2081_78_);
lean_ctor_set(v___x_80_, 1, v_it_u2082_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_append___boxed(lean_object* v_m_81_, lean_object* v_00_u03b2_82_, lean_object* v_00_u03b1_u2081_83_, lean_object* v_00_u03b1_u2082_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_it_u2081_87_, lean_object* v_it_u2082_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_IterM_append(v_m_81_, v_00_u03b2_82_, v_00_u03b1_u2081_83_, v_00_u03b1_u2082_84_, v_inst_85_, v_inst_86_, v_it_u2081_87_, v_it_u2082_88_);
lean_dec(v_inst_86_);
lean_dec(v_inst_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd___redArg(lean_object* v_it_u2082_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_it_u2082_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd(lean_object* v_m_92_, lean_object* v_00_u03b2_93_, lean_object* v_00_u03b1_u2082_94_, lean_object* v_inst_95_, lean_object* v_00_u03b1_u2081_96_, lean_object* v_it_u2082_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_it_u2082_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_appendSnd___boxed(lean_object* v_m_99_, lean_object* v_00_u03b2_100_, lean_object* v_00_u03b1_u2082_101_, lean_object* v_inst_102_, lean_object* v_00_u03b1_u2081_103_, lean_object* v_it_u2082_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_IterM_Intermediate_appendSnd(v_m_99_, v_00_u03b2_100_, v_00_u03b1_u2082_101_, v_inst_102_, v_00_u03b1_u2081_103_, v_it_u2082_104_);
lean_dec(v_inst_102_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__0(lean_object* v_toPure_106_, lean_object* v_____do__lift_107_){
_start:
{
switch(lean_obj_tag(v_____do__lift_107_))
{
case 0:
{
lean_object* v_it_108_; lean_object* v_out_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_118_; 
v_it_108_ = lean_ctor_get(v_____do__lift_107_, 0);
v_out_109_ = lean_ctor_get(v_____do__lift_107_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_____do__lift_107_);
if (v_isSharedCheck_118_ == 0)
{
v___x_111_ = v_____do__lift_107_;
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_out_109_);
lean_inc(v_it_108_);
lean_dec(v_____do__lift_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_it_108_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_out_109_);
v___x_115_ = v_reuseFailAlloc_117_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_apply_2(v_toPure_106_, lean_box(0), v___x_115_);
return v___x_116_;
}
}
}
case 1:
{
lean_object* v_it_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
v_it_119_ = lean_ctor_get(v_____do__lift_107_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v_____do__lift_107_);
if (v_isSharedCheck_128_ == 0)
{
v___x_121_ = v_____do__lift_107_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_it_119_);
lean_dec(v_____do__lift_107_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_it_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_127_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_apply_2(v_toPure_106_, lean_box(0), v___x_125_);
return v___x_126_;
}
}
}
default: 
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(2);
v___x_130_ = lean_apply_2(v_toPure_106_, lean_box(0), v___x_129_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__1(lean_object* v_a_131_, lean_object* v_toPure_132_, lean_object* v_____do__lift_133_){
_start:
{
switch(lean_obj_tag(v_____do__lift_133_))
{
case 0:
{
lean_object* v_it_134_; lean_object* v_out_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_144_; 
v_it_134_ = lean_ctor_get(v_____do__lift_133_, 0);
v_out_135_ = lean_ctor_get(v_____do__lift_133_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_____do__lift_133_);
if (v_isSharedCheck_144_ == 0)
{
v___x_137_ = v_____do__lift_133_;
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_out_135_);
lean_inc(v_it_134_);
lean_dec(v_____do__lift_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_it_134_);
lean_ctor_set(v___x_139_, 1, v_a_131_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_out_135_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_141_);
return v___x_142_;
}
}
}
case 1:
{
lean_object* v_it_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
v_it_145_ = lean_ctor_get(v_____do__lift_133_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_____do__lift_133_);
if (v_isSharedCheck_154_ == 0)
{
v___x_147_ = v_____do__lift_133_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_it_145_);
lean_dec(v_____do__lift_133_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_it_145_);
lean_ctor_set(v___x_149_, 1, v_a_131_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_153_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_151_);
return v___x_152_;
}
}
}
default: 
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_a_131_);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
v___x_157_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg___lam__2(lean_object* v_toPure_158_, lean_object* v_inst_159_, lean_object* v_toBind_160_, lean_object* v_inst_161_, lean_object* v___f_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v_a_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v___f_162_);
lean_dec(v_inst_161_);
v_a_164_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_a_164_);
v_a_165_ = lean_ctor_get(v_x_163_, 1);
lean_inc(v_a_165_);
lean_dec_ref(v_x_163_);
v___f_166_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_166_, 0, v_a_165_);
lean_closure_set(v___f_166_, 1, v_toPure_158_);
v___x_167_ = lean_apply_1(v_inst_159_, v_a_164_);
v___x_168_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v___x_167_, v___f_166_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_inst_159_);
lean_dec(v_toPure_158_);
v_a_169_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v_x_163_);
v___x_170_ = lean_apply_1(v_inst_161_, v_a_169_);
v___x_171_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v___x_170_, v___f_162_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator___redArg(lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_){
_start:
{
lean_object* v_toApplicative_175_; lean_object* v_toBind_176_; lean_object* v_toPure_177_; lean_object* v___f_178_; lean_object* v___f_179_; 
v_toApplicative_175_ = lean_ctor_get(v_inst_172_, 0);
lean_inc_ref(v_toApplicative_175_);
v_toBind_176_ = lean_ctor_get(v_inst_172_, 1);
lean_inc(v_toBind_176_);
lean_dec_ref(v_inst_172_);
v_toPure_177_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_177_);
lean_dec_ref(v_toApplicative_175_);
lean_inc(v_toPure_177_);
v___f_178_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_178_, 0, v_toPure_177_);
v___f_179_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__2), 6, 5);
lean_closure_set(v___f_179_, 0, v_toPure_177_);
lean_closure_set(v___f_179_, 1, v_inst_173_);
lean_closure_set(v___f_179_, 2, v_toBind_176_);
lean_closure_set(v___f_179_, 3, v_inst_174_);
lean_closure_set(v___f_179_, 4, v___f_178_);
return v___f_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIterator(lean_object* v_m_180_, lean_object* v_00_u03b2_181_, lean_object* v_00_u03b1_u2081_182_, lean_object* v_00_u03b1_u2082_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_){
_start:
{
lean_object* v_toApplicative_187_; lean_object* v_toBind_188_; lean_object* v_toPure_189_; lean_object* v___f_190_; lean_object* v___f_191_; 
v_toApplicative_187_ = lean_ctor_get(v_inst_184_, 0);
lean_inc_ref(v_toApplicative_187_);
v_toBind_188_ = lean_ctor_get(v_inst_184_, 1);
lean_inc(v_toBind_188_);
lean_dec_ref(v_inst_184_);
v_toPure_189_ = lean_ctor_get(v_toApplicative_187_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_187_);
lean_inc(v_toPure_189_);
v___f_190_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_190_, 0, v_toPure_189_);
v___f_191_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__2), 6, 5);
lean_closure_set(v___f_191_, 0, v_toPure_189_);
lean_closure_set(v___f_191_, 1, v_inst_185_);
lean_closure_set(v___f_191_, 2, v_toBind_188_);
lean_closure_set(v___f_191_, 3, v_inst_186_);
lean_closure_set(v___f_191_, 4, v___f_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_192_, lean_object* v_recur_193_, lean_object* v_it_194_, lean_object* v_____do__lift_195_){
_start:
{
if (lean_obj_tag(v_____do__lift_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; 
lean_dec_ref(v_it_194_);
lean_dec(v_recur_193_);
v_a_196_ = lean_ctor_get(v_____do__lift_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v_____do__lift_195_);
v___x_197_ = lean_apply_2(v_toPure_192_, lean_box(0), v_a_196_);
return v___x_197_;
}
else
{
lean_object* v_a_198_; lean_object* v___x_199_; 
lean_dec(v_toPure_192_);
v_a_198_ = lean_ctor_get(v_____do__lift_195_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v_____do__lift_195_);
v___x_199_ = lean_apply_4(v_recur_193_, v_it_194_, v_a_198_, lean_box(0), lean_box(0));
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_200_, lean_object* v_recur_201_, lean_object* v___y_202_, lean_object* v_acc_203_, lean_object* v_toBind_204_, lean_object* v_s_205_){
_start:
{
switch(lean_obj_tag(v_s_205_))
{
case 0:
{
lean_object* v_it_206_; lean_object* v_out_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_it_206_ = lean_ctor_get(v_s_205_, 0);
lean_inc(v_it_206_);
v_out_207_ = lean_ctor_get(v_s_205_, 1);
lean_inc(v_out_207_);
lean_dec_ref(v_s_205_);
v___f_208_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_208_, 0, v_toPure_200_);
lean_closure_set(v___f_208_, 1, v_recur_201_);
lean_closure_set(v___f_208_, 2, v_it_206_);
v___x_209_ = lean_apply_3(v___y_202_, v_out_207_, lean_box(0), v_acc_203_);
v___x_210_ = lean_apply_4(v_toBind_204_, lean_box(0), lean_box(0), v___x_209_, v___f_208_);
return v___x_210_;
}
case 1:
{
lean_object* v_it_211_; lean_object* v___x_212_; 
lean_dec(v_toBind_204_);
lean_dec(v___y_202_);
lean_dec(v_toPure_200_);
v_it_211_ = lean_ctor_get(v_s_205_, 0);
lean_inc(v_it_211_);
lean_dec_ref(v_s_205_);
v___x_212_ = lean_apply_4(v_recur_201_, v_it_211_, v_acc_203_, lean_box(0), lean_box(0));
return v___x_212_;
}
default: 
{
lean_object* v___x_213_; 
lean_dec(v_toBind_204_);
lean_dec(v___y_202_);
lean_dec(v_recur_201_);
v___x_213_ = lean_apply_2(v_toPure_200_, lean_box(0), v_acc_203_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4(lean_object* v_inst_214_, lean_object* v_toPure_215_, lean_object* v___y_216_, lean_object* v_toBind_217_, lean_object* v_inst_218_, lean_object* v_lift_219_, lean_object* v_inst_220_, lean_object* v_it_221_, lean_object* v_acc_222_, lean_object* v_hP_223_, lean_object* v_recur_224_){
_start:
{
lean_object* v_toApplicative_225_; lean_object* v_toBind_226_; lean_object* v_toPure_227_; lean_object* v___f_228_; 
v_toApplicative_225_ = lean_ctor_get(v_inst_214_, 0);
lean_inc_ref(v_toApplicative_225_);
v_toBind_226_ = lean_ctor_get(v_inst_214_, 1);
lean_inc(v_toBind_226_);
lean_dec_ref(v_inst_214_);
v_toPure_227_ = lean_ctor_get(v_toApplicative_225_, 1);
lean_inc(v_toPure_227_);
lean_dec_ref(v_toApplicative_225_);
v___f_228_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_228_, 0, v_toPure_215_);
lean_closure_set(v___f_228_, 1, v_recur_224_);
lean_closure_set(v___f_228_, 2, v___y_216_);
lean_closure_set(v___f_228_, 3, v_acc_222_);
lean_closure_set(v___f_228_, 4, v_toBind_217_);
if (lean_obj_tag(v_it_221_) == 0)
{
lean_object* v_a_229_; lean_object* v_a_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_inst_220_);
v_a_229_ = lean_ctor_get(v_it_221_, 0);
lean_inc(v_a_229_);
v_a_230_ = lean_ctor_get(v_it_221_, 1);
lean_inc(v_a_230_);
lean_dec_ref(v_it_221_);
v___f_231_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_231_, 0, v_a_230_);
lean_closure_set(v___f_231_, 1, v_toPure_227_);
v___x_232_ = lean_apply_1(v_inst_218_, v_a_229_);
v___x_233_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_232_, v___f_231_);
v___x_234_ = lean_apply_4(v_lift_219_, lean_box(0), lean_box(0), v___f_228_, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v_a_235_; lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_inst_218_);
v_a_235_ = lean_ctor_get(v_it_221_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v_it_221_);
v___f_236_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_236_, 0, v_toPure_227_);
v___x_237_ = lean_apply_1(v_inst_220_, v_a_235_);
v___x_238_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_237_, v___f_236_);
v___x_239_ = lean_apply_4(v_lift_219_, lean_box(0), lean_box(0), v___f_228_, v___x_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2(lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_lift_244_, lean_object* v_00_u03b3_245_, lean_object* v_Pl_246_, lean_object* v_it_247_, lean_object* v_init_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_toApplicative_250_; lean_object* v_toBind_251_; lean_object* v_toPure_252_; lean_object* v___f_253_; lean_object* v___x_254_; 
v_toApplicative_250_ = lean_ctor_get(v_inst_240_, 0);
lean_inc_ref(v_toApplicative_250_);
v_toBind_251_ = lean_ctor_get(v_inst_240_, 1);
lean_inc(v_toBind_251_);
lean_dec_ref(v_inst_240_);
v_toPure_252_ = lean_ctor_get(v_toApplicative_250_, 1);
lean_inc(v_toPure_252_);
lean_dec_ref(v_toApplicative_250_);
v___f_253_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_253_, 0, v_inst_241_);
lean_closure_set(v___f_253_, 1, v_toPure_252_);
lean_closure_set(v___f_253_, 2, v___y_249_);
lean_closure_set(v___f_253_, 3, v_toBind_251_);
lean_closure_set(v___f_253_, 4, v_inst_242_);
lean_closure_set(v___f_253_, 5, v_lift_244_);
lean_closure_set(v___f_253_, 6, v_inst_243_);
v___x_254_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_253_, v_it_247_, v_init_248_, lean_box(0));
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop___redArg(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_259_, 0, v_inst_256_);
lean_closure_set(v___f_259_, 1, v_inst_255_);
lean_closure_set(v___f_259_, 2, v_inst_257_);
lean_closure_set(v___f_259_, 3, v_inst_258_);
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instIteratorLoop(lean_object* v_m_260_, lean_object* v_00_u03b2_261_, lean_object* v_00_u03b1_u2081_262_, lean_object* v_00_u03b1_u2082_263_, lean_object* v_n_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_){
_start:
{
lean_object* v___f_269_; 
v___f_269_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_269_, 0, v_inst_266_);
lean_closure_set(v___f_269_, 1, v_inst_265_);
lean_closure_set(v___f_269_, 2, v_inst_267_);
lean_closure_set(v___f_269_, 3, v_inst_268_);
return v___f_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation(lean_object* v_00_u03b1_u2081_270_, lean_object* v_00_u03b1_u2082_271_, lean_object* v_m_272_, lean_object* v_00_u03b2_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(lean_object* v_00_u03b1_u2081_280_, lean_object* v_00_u03b1_u2082_281_, lean_object* v_m_282_, lean_object* v_00_u03b2_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_inst_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_Iterators_Types_Append_instFinitenessRelation(v_00_u03b1_u2081_280_, v_00_u03b1_u2082_281_, v_m_282_, v_00_u03b2_283_, v_inst_284_, v_inst_285_, v_inst_286_, v_inst_287_, v_inst_288_);
lean_dec(v_inst_286_);
lean_dec(v_inst_285_);
lean_dec_ref(v_inst_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(lean_object* v_00_u03b1_u2081_290_, lean_object* v_00_u03b1_u2082_291_, lean_object* v_m_292_, lean_object* v_00_u03b2_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_box(0);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(lean_object* v_00_u03b1_u2081_300_, lean_object* v_00_u03b1_u2082_301_, lean_object* v_m_302_, lean_object* v_00_u03b2_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(v_00_u03b1_u2081_300_, v_00_u03b1_u2082_301_, v_m_302_, v_00_u03b2_303_, v_inst_304_, v_inst_305_, v_inst_306_, v_inst_307_, v_inst_308_);
lean_dec(v_inst_306_);
lean_dec(v_inst_305_);
lean_dec_ref(v_inst_304_);
return v_res_309_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
